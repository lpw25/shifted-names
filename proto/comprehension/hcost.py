"""Operation counts for HNorm (Core/HNorm.v), to find and remove super-quadratic costs.

A mirror of HNorm on expressions: words are hash-consed (a word is an id; cell ids are interned),
values are interned, and every basic operation the Coq code does is counted:

  stop    steps a push walks past (and rebuilds)
  hcons   cells consed
  walk    cells a lookup visits
  cmp     label comparisons when a lookup checks a step against the kept labels
  dedup   label comparisons de-duplicating kept labels (Coq: a list, existsb)
  unbound cells visited by clean / has_unbound

Lookup strategies (class attribute `follow`):
  'coq'   HNorm.follow as in Coq: kept labels each once, merged lazily, checked by scanning.
  'fast'  the same results, with summaries of cells computed once per cell: the labels present
          (labs), the next step a lookup of h must look at (nextstop, memoised per (h, cell)),
          a payload memoised per (h, stuck cell), and a trimming walk that stops once no label
          still to come could be passed (trim).  Also a flag per cell for clean.

python3 hcost.py [family ...]   counts at doubling sizes for the benchmark families.
"""
import sys
from collections import Counter

# ---------------------------------------------------------------- expressions (as HBase.v)
# ('id',) ('comp', a, b) ('outer', h, a) ('inner', h, t, a) ('lift', h, a) ('atom', n)
# t: ('var', h, i) | ('bind', u)
ID = ('id',)
def comp(a, b): return ('comp', a, b)
def a_(k): return f'a{k}'
def W(h): return ('outer', h, ID)
def E(h, z): return ('inner', h, ('var', z, 0), ID)
def Ep(h): return ('inner', h, ('bind', 0), ID)
nx = lambda k: 0 if k == 7 else k + 1
n7 = lambda k: 0 if k == 6 else k + 1
n4 = lambda k: 0 if k == 3 else k + 1

def lifts(n, k, b):
    e = b; ks = []
    for _ in range(n): ks.append(k); k = n7(k)
    for k in reversed(ks): e = ('lift', a_(k), e)
    return e
def seqw(n, k, g):
    ks = []
    for _ in range(n): ks.append(k); k = n4(k)
    e = ID
    for k in reversed(ks): e = comp(e, g(k))       # seqw n k g = comp (seqw n' (n4 k) g) (g k)
    return e
def chain(n, k):
    ks = []
    for _ in range(n): ks.append(k); k = nx(k)
    e = ID
    for k in reversed(ks): e = comp(e, comp(E(a_(k), a_(nx(k))), W(a_(n7(n7(n7(k)))))))
    return e
def blocked(n, k):
    ks = []
    for _ in range(n): ks.append(k); k = n7(k)
    e = W(a_(7))
    for k in reversed(ks): e = comp(e, E(a_(k), a_(0)))
    return e
def ren(n, k):
    ks = []
    for _ in range(n): ks.append(k); k = nx(k)
    e = ID
    for k in reversed(ks): e = comp(e, comp(E(a_(nx(k)), a_(k)), W(a_(k))))
    return e

FORD = [(a_(i), a_(i + 1)) for i in range(7)]

def word_expr(steps):
    """The expression of a word, first step first (comp a b is the word of b, then a)."""
    e = None
    for st in steps: e = st if e is None else comp(st, e)
    return e or ID

def adv_labels(n):
    """Many labels.  m = n/3 labels c (not ordered against x, nor each other), m labels b
    (ordered against x and every c, not each other), m labels y (before x and every c):
    entries on the y with value x0, in front of weakenings on every c, then every b.
    Each lookup of x0 passes the y entries, keeps every c, and checks each b against
    every kept c before passing it."""
    m = n // 3
    c = [f'c{j}' for j in range(m)]; b = [f'b{j}' for j in range(m)]; y = [f'y{j}' for j in range(m)]
    steps = [E(yj, 'x') for yj in y] + [W(ci) for ci in c] + [W(bj) for bj in b]
    return word_expr(steps)
def adv_cells(n):
    """As adv_labels, but each lookup is stuck at a different cell: the entry on y_j comes just
    before the weakening on c_j, so the lookup at it keeps c_j, ..., c_m and checks every b."""
    m = n // 3
    c = [f'c{j}' for j in range(m)]; b = [f'b{j}' for j in range(m)]; y = [f'y{j}' for j in range(m)]
    steps = []
    for j in range(m): steps += [E(y[j], 'x'), W(c[j])]
    return word_expr(steps + [W(bj) for bj in b])
def adv_cells_facts(n): return adv_labels_facts(n)
def adv_rebuild(n):
    """advC, with a weakening on z (after every other label) pushed after each lookup: it lands
    at the end of the word, so every cell in front of it is rebuilt, although no cone changes."""
    m = n // 4
    c = [f'c{j}' for j in range(m)]; b = [f'b{j}' for j in range(m)]; y = [f'y{j}' for j in range(m)]
    steps = []
    for j in range(m): steps += [W('z'), E(y[j], 'x'), W(c[j])]
    return word_expr(steps + [W(bj) for bj in b])
def adv_rebuild_facts(n):
    m = n // 4
    labs = [f'c{j}' for j in range(m)] + [f'b{j}' for j in range(m)] + [f'y{j}' for j in range(m)] + ['x']
    return adv_labels_facts(n * 3 // 4) + [(l, 'z') for l in labs]
def adv_nested(n):
    """Lookups of different labels h_j, each able to pass a different nested set of b's, with O(m)
    facts: c's below the hub chain g_0 < g_1 < ..., g_k < b_k, h_j < g_(j+1), e below every h.
    Entries on e with value h_j, in front of weakenings on every c (an antichain), then every b
    (an antichain above every c).  The lookup of h_j keeps every c and can pass b_(j+1), ...: each
    c kept filters that set, without changing it."""
    m = n // 3
    return word_expr([E('e', f'h{j}') for j in range(m)] + [W(f'c{i}') for i in range(m)] +
                     [W(f'b{k}') for k in range(m)])
def adv_nested_facts(n):
    m = n // 3
    F = [(f'c{i}', 'g0') for i in range(m)] + [(f'g{k}', f'g{k+1}') for k in range(m)]
    F += [(f'g{k}', f'b{k}') for k in range(m)] + [(f'h{j}', f'g{j+1}') for j in range(m)]
    F += [('e', f'h{j}') for j in range(m)]
    return F
def many_blocks(n):
    """Few labels, many blocks: c1 and c2 are not ordered, both sort before h; y is not ordered
    against anything.  Weakenings alternating on c1 and c2 (each its own block), then n weakenings
    on h, each pushed past every c block, then n entries on y with value h0, each looking h up past
    every c block."""
    m = n // 3
    return word_expr([E('y', 'h') for _ in range(m)] + [W('h') for _ in range(m)] +
                     [W('c1') if j % 2 == 0 else W('c2') for j in range(m)])
def many_blocks_facts(n): return [('c1', 'h'), ('c2', 'h')]
def adv_labels_facts(n):
    m = n // 3
    c = [f'c{j}' for j in range(m)]; b = [f'b{j}' for j in range(m)]; y = [f'y{j}' for j in range(m)]
    return [('x', bj) for bj in b] + [(ci, bj) for ci in c for bj in b] + [(yj, 'x') for yj in y] + \
           [(yj, ci) for yj in y for ci in c] + [(yj, bj) for yj in y for bj in b]
FAMILIES = {
    'ren':     (lambda n: ren(n, 0), FORD),
    'renU':    (lambda n: ren(n, 0), []),
    'absorbL': (lambda n: lifts(n, 0, W(a_(7))), FORD),
    'wideWE':  (lambda n: comp(seqw(n, 0, lambda k: W(a_(k))), seqw(n, 0, lambda k: E(a_(4 + k), a_(4 + k)))), FORD),
    'wideEW':  (lambda n: comp(seqw(n, 0, lambda k: E(a_(4 + k), a_(4 + k))), seqw(n, 0, lambda k: W(a_(k)))), FORD),
    'payW':    (lambda n: comp(seqw(n, 0, lambda k: Ep(a_(4 + k))), seqw(n, 0, lambda k: W(a_(k)))), FORD),
    'payL':    (lambda n: lifts(n, 0, seqw(4, 0, lambda k: Ep(a_(4 + k)))), FORD),
    'chain':   (lambda n: chain(n, 0), FORD),
    'blocked': (lambda n: blocked(n, 0), []),
    'advL':    (adv_labels, None),       # facts depend on n
    'advC':    (adv_cells, None),
    'manyB':   (many_blocks, None),
    'advR':    (adv_rebuild, None),
    'advN':    (adv_nested, None),
}

# ---------------------------------------------------------------- the normaliser
BOUND = None

class H:
    follow = 'coq'

    def __init__(s, facts):
        succ = {}
        for a, b in facts: succ.setdefault(a, set()).add(b)
        lt = set()
        for a in list(succ):                      # reachability from each label
            seen = set(); todo = list(succ[a])
            while todo:
                x = todo.pop()
                if x in seen: continue
                seen.add(x); todo.extend(succ.get(x, ()))
            lt |= {(a, x) for x in seen}
        s.lt = lt
        s.C = Counter()
        s.cells = {}          # (step, tail id) -> id      (hash-consing)
        s.cell = {1: None}    # id -> (step, tail id); 1 is the empty word
        s.vals = {}           # value -> id

    # labels
    def before(s, a, b): return a != b and (a, b) in s.lt
    def kd(s, a, b): return a != b and ((a, b) in s.lt or (b, a) in s.lt)

    # words
    def hcons(s, st, w):
        s.C['hcons'] += 1
        k = (st, w)
        i = s.cells.get(k)
        if i is None:
            i = len(s.cell) + 1; s.cells[k] = i; s.cell[i] = k
        return i
    def rebuild(s, pre, w):
        for st in reversed(pre): w = s.hcons(st, w)
        return w
    def steps(s, w):
        while w != 1:
            st, w2 = s.cell[w]; yield st, w, w2; w = w2
    def val(s, v): return s.vals.setdefault(v, ('#', len(s.vals)))

    # lookups
    def lookup(s, h, i, w):
        s.C['lookups'] += 1
        return getattr(s, 'follow_' + s.follow)(h, i, w)

    def follow_coq(s, h, i, w):
        kept = []; labs = []; pend = []; n = 0; mark = w
        for st, cur, nxt in s.steps(w):
            s.C['walk'] += 1
            if st[0] == 'A': return s.payload(h, i, kept, n, mark)
            g = st[1]
            # decide
            p = False
            if s.kd(h, g):
                for x in pend:                               # merge: addl each pending label
                    found = False
                    for m in labs:
                        s.C['dedup'] += 1
                        if m == x: found = True; break
                    if not found: labs.insert(0, x)
                pend = []
                p = True
                for m in labs:
                    s.C['cmp'] += 1
                    if not s.kd(g, m): p = False; break
            if p: n = 0; mark = nxt; continue
            if not kept:
                if g == h:
                    if st[0] == 'E':
                        if i == 0: return st[2]
                        i -= 1
                    else: i += 1
                    mark = nxt; continue
                kept = [st]; pend = [g]; n = 1                # mark stays at this cell
            else:
                kept.insert(0, st); pend.insert(0, g); n += 1
        if not kept: return s.val(('V', h, i))
        return s.payload(h, i, kept, n, mark)

    # ------------------------------------------------------------ summaries of cells (lazy, memoised)
    # labs(c): the labels of the steps of c before its first atom.  Coq: a persistent map, one
    # insertion per cell.
    def labs(s, c):
        m = s.__dict__.setdefault('_labs', {1: frozenset()})
        todo = []
        while c not in m: todo.append(c); c = s.cell[c][1]
        for c in reversed(todo):
            st, w = s.cell[c]; s.C['summ'] += 1
            m[c] = frozenset() if st[0] == 'A' else m[w] | {st[1]}
        return m[c]

    # nextstop(h, c): the first cell of c a lookup of h cannot pass without looking at it: a step
    # on h, on a label not known distinct from h, or an atom.  Memoised per (h, cell), filled
    # along the path walked, so each pair is computed once.
    def nextstop(s, h, c):
        m = s.__dict__.setdefault('_next', {})
        path = []
        while True:
            if c == 1 or (h, c) in m: r = 1 if c == 1 else m[(h, c)]; break
            st, w = s.cell[c]; s.C['nstep'] += 1
            if st[0] == 'A' or st[1] == h or not s.kd(h, st[1]): r = c; break
            path.append(c); c = w
        for x in path: m[(h, x)] = r
        if c != 1: m[(h, c)] = r
        return r

    def follow_fast(s, h, i, w):
        # before anything is kept: jump to the next step that can stop the lookup
        c = w
        while True:
            c = s.nextstop(h, c)
            if c == 1: return s.val(('V', h, i))
            st, nxt = s.cell[c]
            if st[0] != 'A' and st[1] == h:
                if st[0] == 'E':
                    if i == 0: return st[2]
                    i -= 1
                else: i += 1
                c = nxt; continue
            break
        memo = s.__dict__.setdefault('_pay', {})
        if (h, c) in memo: s.C['memo'] += 1; return s.val(('L', h, i, memo[(h, c)]))
        r = s.trim(h, c)
        memo[(h, c)] = r
        s.C['stuck'] += 1
        return s.val(('L', h, i, r))

    def trim(s, h, c):
        """The payload of a lookup of h stuck at cell c: the steps of c that h, or a step kept
        before them, depends on.  live: the labels still to come that are known distinct from h
        and from every kept label; once none is left, the rest is kept whole, and shared."""
        st, nxt = s.cell[c]
        if st[0] == 'A': return c
        S = {st[1]}                                        # kept labels (a map)
        live = {x for x in s.labs(nxt) if s.kd(x, h) and s.kd(x, st[1])}
        s.C['live'] += len(s.labs(nxt))
        pre = []; run = [st]; mark = c                      # kept steps before mark; the run since
        cur = nxt
        while cur != 1 and live:
            t, nx2 = s.cell[cur]; s.C['walk'] += 1
            if t[0] == 'A': break
            g = t[1]
            if g in live:                                  # comparable with h and every kept label
                pre.extend(run); run = []; mark = nx2; cur = nx2; continue
            run.append(t)
            if g not in S:
                S.add(g); s.C['live'] += len(live)
                live = {x for x in live if s.kd(x, g)}
            cur = nx2
            if live and not (live & s.labs(cur)): break     # no live label later: keep the rest
        return s.rebuild(pre, mark)

    def payload(s, h, i, kept, n, mark):
        pre = list(reversed(kept[n:]))                        # rev (skipn n kept)
        r = s.rebuild(pre, mark)
        s.C['stuck'] += 1
        return s.val(('L', h, i, r))

    # pushes
    def stop(s, h, w):
        p = []; r = w
        for st, cur, nxt in s.steps(w):
            if st[0] != 'A' and s.before(st[1], h): p.append(st); r = nxt; s.C['stop'] += 1
            else: break
        return p, r
    def pushW(s, h, w):
        p, r = s.stop(h, w)
        if r != 1:
            st, r2 = s.cell[r]
            if st[0] == 'E' and st[1] == h: return s.rebuild(p, r2)
        return s.rebuild(p, s.hcons(('W', h), r))
    def pushE(s, h, v, w):
        p, r = s.stop(h, w)
        if r != 1:
            st, r2 = s.cell[r]
            if st[0] == 'W' and st[1] == h and v == s.lookup(h, 0, r2): return s.rebuild(p, r2)
        return s.rebuild(p, s.hcons(('E', h, v), r))
    def clean(s, w):
        if s.follow == 'fast':                             # a flag per cell: a bound step before an atom
            m = s.__dict__.setdefault('_hasb', {1: False})
            todo = []
            while w not in m: todo.append(w); w = s.cell[w][1]
            for c in reversed(todo):
                st, t = s.cell[c]; s.C['summ'] += 1
                m[c] = False if st[0] == 'A' else (st[1] == BOUND or m[t])
            if not m[todo[0] if todo else w]: return todo[0] if todo else w
            raise NotImplementedError
        pre = []; has = False
        for st, cur, nxt in s.steps(w):
            s.C['unbound'] += 1
            if st[0] == 'A': break
            if st[1] == BOUND: has = True
        if not has: return w
        raise NotImplementedError

    def tval(s, t, K):
        if t[0] == 'var': return s.lookup(t[1], t[2], K)
        return s.val(('T', t[1], s.clean(K)))

    def norm(s, e, K):
        stack = [(e, None)]
        # iterative to avoid Python recursion limits: evaluate norm e K
        return s._norm(e, K)
    def _norm(s, e, K):
        tag = e[0]
        if tag == 'id': return K
        if tag == 'atom': return s.hcons(('A', e[1]), K)
        if tag == 'comp':
            # left spine iteratively: comp(comp(comp(x, g1), g2), g3): norm g3 (norm g2 (norm g1 (norm x K)))
            parts = []
            while e[0] == 'comp': parts.append(e[2]); e = e[1]
            K = s._norm(e, K)
            for b in reversed(parts): K = s._norm(b, K)
            return K
        if tag == 'outer': return s._norm(e[2], s.pushW(e[1], K))
        if tag == 'inner':
            v = s.tval(e[2], K)
            return s.pushE(e[1], v, s._norm(e[3], K))
        if tag == 'lift':
            v = s.lookup(e[1], 0, K)
            return s.pushE(e[1], v, s._norm(e[2], s.pushW(e[1], K)))
        raise ValueError(tag)

def measure(fam, sizes, follow='coq', keys=('walk', 'cmp', 'dedup', 'stop', 'hcons', 'unbound', 'stuck', 'nstep', 'summ', 'live', 'memo')):
    mk, facts = FAMILIES[fam]
    rows = []
    for n in sizes:
        H.follow = follow
        h = H(facts if facts is not None else globals()[mk.__name__ + '_facts'](n)); h.norm(mk(n), 1)
        rows.append((n, {k: h.C[k] for k in keys}))
    return rows

def growth(rows, key):
    out = []
    for (n0, c0), (n1, c1) in zip(rows, rows[1:]):
        out.append('-' if c0[key] == 0 else f'{c1[key] / c0[key]:.1f}')
    return out

def same(fam, n):
    """Both strategies in one table: equal ids mean equal normal forms."""
    mk, facts = FAMILIES[fam]
    h = H(facts if facts is not None else globals()[mk.__name__ + '_facts'](n))
    H.follow = 'coq'; a = h.norm(mk(n), 1)
    H.follow = 'fast'; b = h.norm(mk(n), 1)
    return a == b

if __name__ == '__main__':
    sys.setrecursionlimit(100000)
    args = sys.argv[1:]
    follow = 'coq'
    if args and args[0] in ('coq', 'fast'): follow = args.pop(0)
    fams = args or list(FAMILIES)
    sizes = [125, 250, 500, 1000]
    for f in fams:
        rows = measure(f, sizes, follow)
        print(f'{f} ({follow}):')
        for key in ('walk', 'cmp', 'dedup', 'stop', 'hcons', 'unbound', 'stuck', 'nstep', 'summ', 'live', 'memo'):
            vals = [r[1][key] for r in rows]
            if any(vals): print(f'   {key:8s} {vals}  growth x{" x".join(growth(rows, key))}')
