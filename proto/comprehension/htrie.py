"""HNorm with words stored as blocks, each a hash-consed treap keyed by label (prototype).

A normal word (sorted, reduced) is split wherever two adjacent steps are on different labels not
known to be ordered.  Between splits, adjacent labels are ordered and do not decrease, so (the
order being transitive) a block's labels form a chain, its steps on one label are contiguous, and
by beta they are entries followed by weakenings.  A block is stored as a treap keyed by label in
chain order, with priorities from the labels, so its shape is a function of its content and it can
be hash-consed; each label carries its entries (a hash-consed list of values) and its number of
weakenings.  A word is a hash-consed list of blocks and atoms.  Splits are local: an edit to one
block can only merge it with a neighbour.

Operations (the normal forms are those of hcost.H; see check()):
  push of a step on h   pass whole blocks whose labels all sort before h, then one O(log) edit
  lookup of h           in a block: labels before h, then h or labels not ordered against h,
                        then labels after h; one descent tells which
  stuck lookup          the payload is the cone of h (see K below), memoised per (label, cell),
                        so lookups stuck at different cells of the same tail share their work
                        (mode 'walk': the older trimming walk, kept for comparison)

Counts: blocks (blocks walked), tcmp (label comparisons in treap descents), tnode (treap nodes
built), lcell (list cells built), idx (entries walked to an index), live (label tests).

python3 htrie.py [family ...]   counts at doubling sizes; python3 htrie.py check   compare with hcost
"""
import sys, zlib
from collections import Counter
import hcost
from hcost import FAMILIES


def prio(label):
    return zlib.crc32(str(label).encode())


class T:
    mode = 'cone'                                      # stuck lookups: 'cone' or 'walk' (trim)

    def __init__(s, facts):
        s.base = hcost.H(facts)                   # for the order
        s.lt = s.base.lt
        s.C = Counter()
        s.vals = {}; s.valof = []                 # value -> id
        s.lists = {(): 0}; s.listof = [None]      # entries: id -> (value id, tail id, length)
        s.nodes = {}; s.nodeof = [None]           # treap: id -> (label, seq, left, right, first, last, labs, size)
        s.cells = {}; s.cellof = [None, None]     # word: id -> (item, tail); 1 is the empty word
        s.clabs = {1: frozenset()}                # labels of a word before its first atom
        s.paymemo = {}

    # ---------------------------------------------------------------- order
    def before(s, a, b):
        s.C['tcmp'] += 1
        return a != b and (a, b) in s.lt
    def kd(s, a, b): return a != b and ((a, b) in s.lt or (b, a) in s.lt)

    # ---------------------------------------------------------------- values and entry lists
    def val(s, v):
        i = s.vals.get(v)
        if i is None: i = len(s.valof); s.vals[v] = i; s.valof.append(v)
        return i
    def econs(s, v, tl):
        k = (v, tl); i = s.lists.get(k)
        if i is None:
            i = len(s.listof); s.lists[k] = i
            s.listof.append((v, tl, 1 + (s.listof[tl][2] if tl else 0)))
        return i
    def elen(s, l): return s.listof[l][2] if l else 0
    def enth(s, l, i):
        while i: s.C['idx'] += 1; l = s.listof[l][1]; i -= 1
        return s.listof[l][0]

    # ---------------------------------------------------------------- treaps (blocks)
    def mk(s, k, seq, l, r):
        key = (k, seq, l, r); i = s.nodes.get(key)
        if i is None:
            s.C['tnode'] += 1
            L = s.nodeof[l] if l else None; R = s.nodeof[r] if r else None
            first = L[4] if L else k; last = R[5] if R else k
            labs = (L[6] if L else frozenset()) | (R[6] if R else frozenset()) | {k}
            size = (L[7] if L else 0) + (R[7] if R else 0) + 1
            i = len(s.nodeof); s.nodes[key] = i; s.nodeof.append((k, seq, l, r, first, last, labs, size))
        return i
    def split(s, t, pred):
        """(prefix where pred holds, rest); pred is monotone along the chain."""
        if not t: return 0, 0
        k, seq, l, r = s.nodeof[t][:4]
        if pred(k):
            a, b = s.split(r, pred); return s.mk(k, seq, l, a), b
        a, b = s.split(l, pred); return a, s.mk(k, seq, b, r)
    def join(s, a, b):
        """Every key of a before every key of b."""
        if not a: return b
        if not b: return a
        ka, sa, la, ra = s.nodeof[a][:4]; kb, sb, lb, rb = s.nodeof[b][:4]
        if prio(ka) > prio(kb): return s.mk(ka, sa, la, s.join(ra, b))
        return s.mk(kb, sb, s.join(a, lb), rb)
    def single(s, k, seq): return s.mk(k, seq, 0, 0)
    def first_not_before(s, t, h):
        """The first label of the chain t not sorting before h, or None."""
        best = None
        while t:
            k, seq, l, r = s.nodeof[t][:4]
            if s.before(k, h): t = r
            else: best = k; t = l
        return best
    def find(s, t, k):
        while t:
            k2, seq, l, r = s.nodeof[t][:4]
            if k2 == k: return seq
            if s.before(k, k2): t = l
            elif s.before(k2, k): t = r
            else: return None
        return None
    def setseq(s, t, k, seq):
        """Replace (or with seq None, remove) the entry of k, which t has or which fits its chain."""
        L, R = s.split(t, lambda x: s.before(x, k))
        M, R2 = s.split(R, lambda x: x == k)
        mid = s.single(k, seq) if seq is not None else 0
        return s.join(s.join(L, mid), R2)
    def tlabels(s, t): return s.nodeof[t][6] if t else frozenset()
    def tfirst(s, t): return s.nodeof[t][4]
    def tlast(s, t): return s.nodeof[t][5]
    def inorder(s, t, out):
        if t:
            k, seq, l, r = s.nodeof[t][:4]
            s.inorder(l, out); out.append((k, seq)); s.inorder(r, out)
        return out

    # ---------------------------------------------------------------- words
    def cons(s, item, tl):
        key = (item, tl); i = s.cells.get(key)
        if i is None:
            s.C['lcell'] += 1
            i = len(s.cellof); s.cells[key] = i; s.cellof.append(key)
            s.clabs[i] = frozenset() if item[0] == 'A' else s.tlabels(item[1]) | s.clabs[tl]
        return i
    def cons_block(s, t, w):
        """A block in front of w, merged with w's first block when their ends are ordered."""
        if not t: return w
        if w != 1:
            item, tl = s.cellof[w]
            if item[0] == 'B' and s.kd(s.tlast(t), s.tfirst(item[1])):
                assert s.before(s.tlast(t), s.tfirst(item[1]))
                return s.cons(('B', s.join(t, item[1])), tl)
        return s.cons(('B', t), w)
    def rebuild(s, prev, w):
        for t in reversed(prev): w = s.cons(('B', t), w)
        return w

    def locate(s, h, w):
        """The blocks a step on h passes (all their labels sort before h), and where it stops."""
        prev = []; c = w
        while c != 1:
            item, tl = s.cellof[c]
            if item[0] == 'A': break
            s.C['blocks'] += 1
            f1 = s.first_not_before(item[1], h)
            if f1 is None: prev.append(item[1]); c = tl; continue
            return prev, c, f1
        return prev, c, None

    def push(s, h, w, seqop, fresh):
        """seqop(seq, c): h's new entries and weakenings when the block at c has h (None: none
        left); fresh: the sequence of a new label h."""
        prev, c, f1 = s.locate(h, w)
        if f1 is None:                                     # an atom or the end
            if prev: prev[-1] = s.setseq(prev[-1], h, fresh); return s.rebuild(prev, c)
            return s.cons(('B', s.single(h, fresh)), c)
        t = s.cellof[c][0][1]; tl = s.cellof[c][1]
        if f1 == h:
            new = seqop(s.find(t, h), c)
            t2 = s.setseq(t, h, new)
            if t2: return s.rebuild(prev, s.cons(('B', t2), tl))
            # the block is gone: its neighbours may now be ordered
            if prev: return s.rebuild(prev[:-1], s.cons_block(prev[-1], tl))
            return tl
        if s.before(h, f1):                                # h fits the block
            return s.rebuild(prev, s.cons(('B', s.setseq(t, h, fresh)), tl))
        P, R = s.split(t, lambda x: s.before(x, h))        # f1 not ordered against h: split
        P2 = s.setseq(P, h, fresh)
        if not P and prev: prev[-1] = s.join(prev[-1], P2); P2 = 0
        w2 = s.cons(('B', R), tl)
        if P2: w2 = s.cons(('B', P2), w2)
        return s.rebuild(prev, w2)

    def pushW(s, h, w):
        def op(seq, c):
            ents, b = seq
            if ents: ents = s.listof[ents][1]               # beta: the first entry goes
            else: b += 1
            return (ents, b) if ents or b else None
        return s.push(h, w, op, (0, 1))
    def pushE(s, h, v, w):
        def op(seq, c):
            ents, b = seq
            if not ents and b:                              # eta, against h0 after one weakening
                if v == s.lookup(h, b - 1, s.cellof[c][1]):
                    return (0, b - 1) if b - 1 else None
            return (s.econs(v, ents), b)
        return s.push(h, w, op, (s.econs(v, 0), 0))

    # ---------------------------------------------------------------- lookups
    def lookup(s, h, i, w):
        s.C['lookups'] += 1
        c = w
        while c != 1:
            item, tl = s.cellof[c]
            if item[0] == 'A': return s.val(('L', h, i, c))
            t = item[1]; s.C['blocks'] += 1
            f1 = s.first_not_before(t, h)
            if f1 is None or (f1 != h and s.before(h, f1)): c = tl; continue
            if f1 == h:
                ents, b = s.find(t, h); a = s.elen(ents)
                if i < a: return s.enth(ents, i)
                i = i - a + b; c = tl; continue
            key = (h, c)
            if key not in s.paymemo:
                s.paymemo[key] = s.cword(s.K(h, c)) if s.mode == 'cone' else s.trim(h, t, tl)
            return s.val(('L', h, i, s.paymemo[key]))
        return s.val(('V', h, i))

    def trim(s, h, t, tl):
        """The payload of a lookup of h stuck in block t: the steps that h, or a step kept before
        them, depends on."""
        P, R = s.split(t, lambda x: s.before(x, h))         # passed before getting stuck
        M, Q = s.split(R, lambda x: not s.before(h, x))     # kept: not ordered against h
        pieces = [M]
        S = set(s.tlabels(M))
        live = {x for x in s.clabs[tl] if s.kd(x, h) and all(s.kd(x, m) for m in S)}
        s.C['live'] += len(s.clabs[tl]) * (1 + len(S))
        c = tl
        while c != 1 and live and (live & s.clabs[c]):
            item, nxt = s.cellof[c]
            if item[0] == 'A': break
            B = item[1]; s.C['blocks'] += 1
            passed = s.tlabels(B) & live
            for x in passed: B = s.setseq(B, x, None)
            if B:
                pieces.append(B)
                new = s.tlabels(B) - S
                if new:
                    s.C['live'] += len(live) * len(new)
                    S |= new; live = {x for x in live if all(s.kd(x, m) for m in new)}
            c = nxt
        w = c
        for piece in reversed(pieces): w = s.cons_block(piece, w)
        return w

    # ---------------------------------------------------------------- cones (trim='cone')
    # K(x, c): the (block cell, label) pairs of c that a step on x in front of c reaches through
    # dependence.  In a block the labels dependent on x are those neither before nor after x: a
    # contiguous range of its chain.  With t the first block of c that has one (nextdep):
    #     K(x, c) = {(t, l) : l in range} u K(x, after t) u U_{l in range} K(l, after t)
    # memoised per (label, cell).  A cone is stored as (E, tail): every block from the cell tail
    # on, and the pairs E before it.
    def depth(s, c):
        m = s.__dict__.setdefault('_depth', {1: 0})
        todo = []
        while c not in m: todo.append(c); c = s.cellof[c][1]
        for x in reversed(todo): m[x] = m[s.cellof[x][1]] + 1
        return m[todo[0]] if todo else m[c]
    def middle(s, t, x):
        P, R = s.split(t, lambda y: s.before(y, x))
        M, Q = s.split(R, lambda y: not s.before(x, y))
        return M
    def nextdep(s, x, c):
        m = s.__dict__.setdefault('_nd', {})
        path = []
        while True:
            if c == 1 or (x, c) in m: r = 1 if c == 1 else m[(x, c)]; break
            item, tl = s.cellof[c]; s.C['nd'] += 1
            if item[0] == 'A': r = c; break
            f1 = s.first_not_before(item[1], x)
            if f1 is not None and (f1 == x or not s.before(x, f1)): r = c; break
            path.append(c); c = tl
        for p in path: m[(x, p)] = r
        if c != 1: m[(x, c)] = r
        return r
    # Cones as hash-consed Patricia tries (big-endian, integer keys): key = depth * W + label
    # index, leaf value (cell, label).  Union is memoised and returns at once on equal ids, so
    # cones built from shared tails share structure.  A cone is (trie, tail): with an atom, every
    # block from the atom on (tail; 1 if none) as well.
    W = 1 << 20
    def lidx(s, l):
        m = s.__dict__.setdefault('_lidx', {})
        return m.setdefault(l, len(m))
    def tnew(s, node):
        tm = s.__dict__.setdefault('_tm', {})
        tl = s.__dict__.setdefault('_tl', [None])
        tc = s.__dict__.setdefault('_tc', [0])
        i = tm.get(node)
        if i is None:
            i = len(tl); tm[node] = i; tl.append(node); s.C['pnode'] += 1
            tc.append(1 if node[0] == 'L' else tc[node[3]] + tc[node[4]])
        return i
    def tbelow(s, t, K):
        """The number of keys of t below K."""
        n = 0
        while t:
            s.C['tq'] += 1
            nd = s._tl[t]
            if nd[0] == 'L': return n + (nd[1] < K)
            pre, m, l, r = nd[1:]
            if K & ~((m << 1) - 1) != pre: return n + (s._tc[t] if pre < K else 0)
            if K & m: n += s._tc[l]; t = r
            else: t = l
        return n
    def tany(s, t, lo, hi):
        """The value of some key of t in [lo, hi), or None."""
        if not t: return None
        s.C['tq'] += 1
        nd = s._tl[t]
        if nd[0] == 'L': return nd[2] if lo <= nd[1] < hi else None
        pre, m, l, r = nd[1:]
        top = pre | ((m << 1) - 1)
        if top < lo or pre >= hi: return None
        v = s.tany(l, lo, hi)
        return v if v is not None else s.tany(r, lo, hi)
    def tfrom(s, t, K, out):
        """The values of the keys of t at least K."""
        if t:
            nd = s._tl[t]
            if nd[0] == 'L':
                if nd[1] >= K: out.append(nd[2]); s.C['enum'] += 1
            else:
                pre, m, l, r = nd[1:]
                if (pre | ((m << 1) - 1)) >= K: s.C['tq'] += 1; s.tfrom(l, K, out); s.tfrom(r, K, out)
        return out
    def csize(s, c):
        m = s.__dict__.setdefault('_cs', {1: 0})
        todo = []
        while c not in m: todo.append(c); c = s.cellof[c][1]
        for x in reversed(todo):
            item, tl = s.cellof[x]
            m[x] = m[tl] + (0 if item[0] == 'A' else len(s.tlabels(item[1])))
        return m[todo[0]] if todo else m[c]
    def tleaf(s, key, val): return s.tnew(('L', key, val))
    def tjoin(s, k1, t1, k2, t2):
        x = k1 ^ k2; m = 1 << (x.bit_length() - 1); pre = k1 & ~((m << 1) - 1)
        return s.tnew(('B', pre, m, t1, t2) if k1 & m == 0 else ('B', pre, m, t2, t1))
    def tkey(s, t):
        n = s._tl[t]; return n[1]
    def tunion(s, a, b):
        if a == b or not b: return a
        if not a: return b
        um = s.__dict__.setdefault('_tu', {})
        k = (a, b) if a < b else (b, a)
        if k in um: return um[k]
        s.C['union'] += 1
        A = s._tl[a]; B = s._tl[b]
        if A[0] == 'L' and B[0] == 'L':
            r = a if A[1] == B[1] else s.tjoin(A[1], a, B[1], b)
        elif A[0] == 'L' or B[0] == 'L':
            if B[0] == 'L': a, b, A, B = b, a, B, A           # A a leaf, B a branch
            pre, m, l, rr = B[1:]
            if A[1] & ~((m << 1) - 1) != pre: r = s.tjoin(A[1], a, pre, b)
            elif A[1] & m == 0: r = s.tnew(('B', pre, m, s.tunion(a, l), rr))
            else: r = s.tnew(('B', pre, m, l, s.tunion(a, rr)))
        else:
            p1, m1, l1, r1 = A[1:]; p2, m2, l2, r2 = B[1:]
            if m1 == m2 and p1 == p2: r = s.tnew(('B', p1, m1, s.tunion(l1, l2), s.tunion(r1, r2)))
            elif m1 > m2 and p2 & ~((m1 << 1) - 1) == p1:
                r = s.tnew(('B', p1, m1, s.tunion(l1, b), r1) if p2 & m1 == 0 else ('B', p1, m1, l1, s.tunion(r1, b)))
            elif m2 > m1 and p1 & ~((m2 << 1) - 1) == p2:
                r = s.tnew(('B', p2, m2, s.tunion(a, l2), r2) if p1 & m2 == 0 else ('B', p2, m2, l2, s.tunion(a, r2)))
            else: r = s.tjoin(p1, a, p2, b)
        um[k] = r
        return r
    def telems(s, t, out):
        if t:
            n = s._tl[t]
            if n[0] == 'L': out.append(n[2])
            else: s.telems(n[3], out); s.telems(n[4], out)
        return out
    def cone(s, trie, tail):
        cs = s.__dict__.setdefault('_cones', {(0, 1): 0})
        cl = s.__dict__.setdefault('_conel', [(0, 1)])
        k = (trie, tail); i = cs.get(k)
        if i is None: i = len(cl); cs[k] = i; cl.append(k)
        return i
    def cunion(s, a, b):
        if a == b or not b: return a
        if not a: return b
        (ta, xa), (tb, xb) = s._conel[a], s._conel[b]
        return s.cone(s.tunion(ta, tb), xa if s.depth(xa) >= s.depth(xb) else xb)
    def own(s, t, labs):
        tr = 0
        for l in labs: tr = s.tunion(tr, s.tleaf(s.depth(t) * s.W + s.lidx(l), (t, l)))
        return s.cone(tr, 1)
    def K(s, x, c):
        km = s.__dict__.setdefault('_km', {})
        chain = []
        while True:
            t = s.nextdep(x, c)
            if t == 1: r = 0; break
            if (x, t) in km: r = km[(x, t)]; break
            item, after = s.cellof[t]
            if item[0] == 'A': r = s.cone(0, t); km[(x, t)] = r; break
            chain.append(t); c = after
        for t in reversed(chain):
            item, after = s.cellof[t]; s.C['kent'] += 1
            labs = s.tlabels(s.middle(item[1], x))
            own = s.own(t, labs)
            for l in labs: own = s.cunion(own, s.K(l, after))
            r = s.cunion(own, r)
            km[(x, t)] = r
        return r
    def tremove_from(s, t, K):
        """t without its keys at least K."""
        if not t: return 0
        nd = s._tl[t]
        if nd[0] == 'L': return 0 if nd[1] >= K else t
        pre, m, l, r = nd[1:]
        if pre >= K: return 0
        if (pre | ((m << 1) - 1)) < K: return t
        s.C['tq'] += 1
        l2, r2 = s.tremove_from(l, K), s.tremove_from(r, K)
        if not l2: return r2
        if not r2: return l2
        return s.tnew(('B', pre, m, l2, r2))
    def cword(s, k):
        """The payload word of cone k: its blocks in order, sharing the longest whole suffix of
        the word it contains (found by binary search on depth, with counts in the trie); the
        rest is the front block on the payload word of the cone without it (memoised by trie,
        so cones that differ in front blocks share the rest)."""
        trie, tail = s._conel[k]
        return s.tword(trie, tail)
    def tword(s, trie, tail):
        wm = s.__dict__.setdefault('_wm', {})
        if (trie, tail) in wm: return wm[(trie, tail)]
        if not trie: return tail
        d0 = s.depth(tail); base = s.csize(tail)
        def full(d):                                       # every block of depth <= d is in the cone
            v = s.tany(trie, d * s.W, (d + 1) * s.W)
            if v is None: return None
            c = v[0]
            n = s.tbelow(trie, (d + 1) * s.W) - s.tbelow(trie, (d0 + 1) * s.W)
            return c if n == s.csize(c) - base else None
        top = s.depth(s.telems_max(trie))
        lo, hi, w = d0, top, tail
        while lo < hi:                                     # largest d in [d0, top] with full(d)
            mid = (lo + hi + 1) // 2
            c = full(mid)
            if c is not None: lo = mid; w = c
            else: hi = mid - 1
        if lo == top: r = w
        else:
            front = s.tfrom(trie, top * s.W, [])           # the front block's labels
            c = front[0][0]; t = s.cellof[c][0][1]; sub = 0
            for (_, l) in front: sub = s.setseq(sub, l, s.find(t, l)); s.C['pword'] += 1
            r = s.cons_block(sub, s.tword(s.tremove_from(trie, top * s.W), tail))
        wm[(trie, tail)] = r
        return r
    def telems_max(s, t):
        while s._tl[t][0] == 'B': t = s._tl[t][4]
        return s._tl[t][2][0]

    # ---------------------------------------------------------------- normalisation
    def tval(s, t, K):
        if t[0] == 'var': return s.lookup(t[1], t[2], K)
        return s.val(('T', t[1], K))                        # no bound labels in these families

    def norm(s, e, K):
        tag = e[0]
        if tag == 'id': return K
        if tag == 'atom': return s.cons(('A', e[1]), K)
        if tag == 'comp':
            parts = []
            while e[0] == 'comp': parts.append(e[2]); e = e[1]
            K = s.norm(e, K)
            for b in reversed(parts): K = s.norm(b, K)
            return K
        if tag == 'outer': return s.norm(e[2], s.pushW(e[1], K))
        if tag == 'inner':
            v = s.tval(e[2], K)
            return s.pushE(e[1], v, s.norm(e[3], K))
        if tag == 'lift':
            v = s.lookup(e[1], 0, K)
            return s.pushE(e[1], v, s.norm(e[2], s.pushW(e[1], K)))
        raise ValueError(tag)

    # ---------------------------------------------------------------- back to plain words
    def to_cells(s, H, w, memo=None):
        """The word w in H's hash-consed cells (H an hcost.H)."""
        memo = {} if memo is None else memo
        def cv(vid):
            v = s.valof[vid]
            if v[0] == 'V': return H.val(v)
            if v[0] == 'T': return H.val(('T', v[1], word(v[2])))
            return H.val((v[0], v[1], v[2], word(v[3])))
        def word(w):
            if w in memo: return memo[w]
            items = []; c = w
            while c != 1 and c not in memo: items.append(c); c = s.cellof[c][1]
            r = 1 if c == 1 else memo[c]
            for c in reversed(items):
                item = s.cellof[c][0]
                if item[0] == 'A': r = H.hcons(('A', item[1]), r)
                else:
                    for k, (ents, b) in reversed(s.inorder(item[1], [])):
                        for _ in range(b): r = H.hcons(('W', k), r)
                        vs = []
                        e = ents
                        while e: vs.append(s.listof[e][0]); e = s.listof[e][1]
                        for v in reversed(vs): r = H.hcons(('E', k, cv(v)), r)
                memo[c] = r
            return r
        return word(w)


def facts_of(fam, n):
    mk, facts = FAMILIES[fam]
    return facts if facts is not None else getattr(hcost, mk.__name__ + '_facts')(n)

def check(fam, n):
    mk, _ = FAMILIES[fam]; facts = facts_of(fam, n)
    H = hcost.H(facts); H.follow = 'coq'; a = H.norm(mk(n), 1)
    tr = T(facts); b = tr.to_cells(H, tr.norm(mk(n), 1))
    return a == b

def measure(fam, sizes, keys=('blocks', 'tcmp', 'tnode', 'lcell', 'idx', 'live', 'kent', 'union', 'pnode', 'tq', 'enum', 'nd', 'pword')):
    mk, _ = FAMILIES[fam]
    rows = []
    for n in sizes:
        tr = T(facts_of(fam, n)); tr.norm(mk(n), 1)
        rows.append((n, {k: tr.C[k] for k in keys}))
    return rows

if __name__ == '__main__':
    sys.setrecursionlimit(100000)
    args = sys.argv[1:]
    if args and args[0] == 'check':
        for f in args[1:] or FAMILIES:
            print(f, [check(f, n) for n in (20, 41, 100, 203)])
        sys.exit()
    for f in args or FAMILIES:
        rows = measure(f, [125, 250, 500, 1000])
        print(f'{f}:')
        for key in ('blocks', 'tcmp', 'tnode', 'lcell', 'idx', 'live', 'kent', 'union', 'pnode', 'tq', 'enum', 'nd', 'pword'):
            vals = [r[1][key] for r in rows]
            if any(vals): print(f'   {key:7s} {vals}  growth x{" x".join(hcost.growth(rows, key))}')
