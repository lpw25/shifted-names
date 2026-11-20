"""The context-form pass, reworked so that a step only touches what moves.

Same forms as forms.py (outputs popped in order; inputs outermost first, each with a target
(z, i, d): the name z_i read after the first d outputs).  Differences:

- The expression is processed from its end, as HNorm does: each new form enters on the left of
  the settled word and its outputs and inputs move right, form by form, as far as they go.
- After an item lands in a form, only the new items are placed: outputs and inputs by insertion,
  new reads taken as early as they can be, new restores (from lifts) absorbed.
- Only items that just arrived are tried against the next form, except where a cancellation or
  a departure may have freed something: then that boundary is looked at again in full.

Items carry ids so that "new" can be tracked across forms.
"""
import itertools
_ids = itertools.count()

class Form:
    __slots__ = ('O', 'I')
    def __init__(s, O, I): s.O = list(O); s.I = list(I)   # O: [(id, label)], I: [(id, label, (z,i,d))]
    def key(s): return (tuple(l for _, l in s.O), tuple((l, t) for _, l, t in s.I))
    def empty(s): return not s.O and not s.I
    def ids(s): return {x for x, _ in s.O} | {x for x, _, _ in s.I}

class Atom:
    __slots__ = ('L', 'n')
    def __init__(s, L, n): s.L = tuple(L); s.n = n
    def key(s): return ('A', s.L, s.n)

class R:
    def __init__(s, n): s.n = n; s.stats = {'moves': 0, 'swaps': 0, 'visits': 0}
    def kd(s, a, b): return s.n.kd(a, b)
    def before(s, a, b): return s.n.before(a, b)

    # ---------- reads ----------
    def nread(s, O, r):
        z, i, d = r
        while d > 0:
            o = O[d - 1][1]
            if o == z: i += 1; d -= 1
            elif s.kd(z, o): d -= 1
            else: break
            s.stats['moves'] += 1
        return (z, i, d)

    # ---------- composing f1 ; f2 (f1 first on variables) ----------
    def compose(s, f1, f2):
        """f1 ; f2 as one form, built in place in f2 (f1 first on variables).
        Returns (f2, new_out_ids, new_in_ids, cancelled), or None leaving f2 unchanged."""
        I2 = f2.I; gone = {}                              # index in I2 -> index of the f1 output that cancelled it
        passed = []
        for j, (oid, o) in enumerate(f1.O):
            for p in range(len(I2)):
                if p in gone: continue
                s.stats['moves'] += 1
                l = I2[p][1]
                if l == o: gone[p] = j; break
                if not s.kd(l, o): return None
            else:
                passed.append((oid, o, j))
        n2 = len(f2.O)
        pj = [j for (_, _, j) in passed]
        npass_before = []; k = 0
        for d in range(len(f1.O) + 1):
            while k < len(pj) and pj[k] < d: k += 1
            npass_before.append(k)
        newI = []
        for (iid, h, (z, i, d)) in f1.I:
            res = None
            for p in range(len(I2)):
                if p in gone and gone[p] < d: continue
                s.stats['moves'] += 1
                jid, l, t = I2[p]
                if l == z:
                    if i == 0: res = t; break
                    i -= 1
                elif not s.kd(l, z): return None
            if res is None: res = (z, i, n2 + npass_before[d])
            newI.append((iid, h, res))
        # build in place
        f2.O.extend((oid, o) for (oid, o, _) in passed)
        for p in sorted(gone, reverse=True): del I2[p]
        if newI: I2[0:0] = newI
        g = f2
        for q in range(len(newI)):
            iid, h, t = g.I[q]; g.I[q] = (iid, h, s.nread(g.O, t))
        # new inputs are outermost, new outputs at the bottom; inputs of f2 may have gone
        s.place_inputs(g, inward=range(len(newI) - 1, -1, -1))
        if gone: s.place_inputs(g, outward=range(len(newI), len(g.I)))
        s.place_outputs(g, up=range(n2, len(g.O)))
        newin = {iid for (iid, _, _) in f1.I}
        s.absorb_new(g, newin)
        return g, {oid for (oid, _, _) in passed}, newin, bool(gone)

    # ---------- placing new items in a form ----------
    def reads_at(s, f):
        r = {}
        for q, (_, _, t) in enumerate(f.I): r.setdefault(t[2], []).append(q)
        return r

    def oswap(s, f, k, ra):
        """Swap outputs k and k+1 if they sort the other way and the reads between allow it."""
        a, b = f.O[k][1], f.O[k + 1][1]
        if not (s.kd(a, b) and s.before(b, a)): return False
        between = ra.get(k + 1, [])
        for q in between:
            z, i, d = f.I[q][2]
            if z == b:
                if i == 0: return False
            elif not s.kd(z, b): return False
        s.stats['swaps'] += 1
        f.O[k], f.O[k + 1] = f.O[k + 1], f.O[k]
        for q in between:
            iid, h, (z, i, d) = f.I[q]
            f.I[q] = (iid, h, (z, i - 1 if z == b else i, k + 2))
        if between:
            del ra[k + 1]; ra.setdefault(k + 2, []).extend(between)
        return True

    def place_outputs(s, f, up=(), down=()):
        """Outputs at positions up (in increasing order) bubble up; at positions down bubble down."""
        ra = None
        for k in up:
            while k > 0:
                if ra is None: ra = s.reads_at(f)
                if not s.oswap(f, k - 1, ra): break
                k -= 1
        for k in down:
            while k + 1 < len(f.O):
                if ra is None: ra = s.reads_at(f)
                if not s.oswap(f, k, ra): break
                k += 1

    def place_inputs(s, f, inward=(), outward=()):
        for k in inward:                                   # in decreasing order
            while k + 1 < len(f.I) and s.before(f.I[k + 1][1], f.I[k][1]):
                s.stats['swaps'] += 1; f.I[k], f.I[k + 1] = f.I[k + 1], f.I[k]; k += 1
        for k in outward:                                  # in increasing order
            while k > 0 and s.before(f.I[k][1], f.I[k - 1][1]):
                s.stats['swaps'] += 1; f.I[k], f.I[k - 1] = f.I[k - 1], f.I[k]; k -= 1

    def absorb_at(s, f, p, lo=0):
        """Input p restores the output its read reaches (only outputs it commutes with between),
        and nothing below or inside stops that output and input from moving to the bottom: drop both."""
        iid, l, (z, i, d) = f.I[p]
        if z != l or i != 0: return False
        j = d
        while j < len(f.O) and f.O[j][1] != l:
            if not s.kd(l, f.O[j][1]): return False
            j += 1
        if j >= len(f.O): return False
        if not all(s.kd(l, o) for _, o in f.O[j + 1:]): return False
        if not all(s.kd(l, m) for _, m, _ in f.I[p + 1:]): return False
        below = [q for q in range(lo, len(f.I)) if f.I[q][2][2] > j and q != p]
        upd = {}
        for q in below:
            jid, m, (y, k, e) = f.I[q]
            if y == l: upd[q] = (jid, m, (y, k + 1, e - 1))
            elif s.kd(y, l): upd[q] = (jid, m, (y, k, e - 1))
            else: return False
        for q, v in upd.items(): f.I[q] = v
        del f.O[j]; del f.I[p]
        for q in range(min(lo, p), len(f.I)):
            jid, m, t = f.I[q]
            if t[2] == j: f.I[q] = (jid, m, s.nread(f.O, t))   # reads the output stopped
        s.place_outputs(f, up=range(j, len(f.O)))
        s.place_inputs(f, outward=range(p, len(f.I)))
        return True

    def absorb_new(s, f, new_in):
        ch = True
        while ch:
            ch = False
            for p, (iid, h, t) in enumerate(f.I):
                if iid in new_in and s.absorb_at(f, p): ch = True; break

    # ---------- moving one item of f on ----------
    def out_first(s, f, j):
        oid, o = f.O[j]
        for _, a in f.O[:j]:
            s.stats['moves'] += 1
            if not s.kd(o, a): return None
        newI = []
        for (iid, h, (z, i, d)) in f.I:
            if d > j: newI.append((iid, h, (z, i, d - 1)))
            elif z == o:
                if i == 0: return None
                newI.append((iid, h, (z, i - 1, d)))
            elif s.kd(z, o): newI.append((iid, h, (z, i, d)))
            else: return None
        return (oid, o), Form(f.O[:j] + f.O[j + 1:], newI)

    def out_alias(s, f1, f2, j):
        """Output j of f1 moves into f2 although inputs of f1 read the value it pops, when f2,
        with that output added, pushes the same value on some label y: those reads are
        redirected to y.  Returns (f1', g, oid) or None (f2 unchanged)."""
        oid, o = f1.O[j]
        for _, a in f1.O[:j]:
            if not s.kd(o, a): return None
        g = Form(list(f2.O), list(f2.I))
        if s.compose(Form([(oid, o)], []), g) is None: return None
        jj = next((q for q, (x, _) in enumerate(g.O) if x == oid), None)
        if jj is None: return None           # cancelled in f2: not this case
        alias = None; seen = {}
        for (iid, y, (z, i, d)) in g.I:
            m = seen.get(y, 0); seen[y] = m + 1
            if z == o and i == 0 and d <= jj and all(s.kd(o, b) and b != o for _, b in g.O[d:jj]):
                alias = (y, m); break
        if alias is None: return None
        newI = []
        for (iid, h, (z, i, d)) in f1.I:
            if d > j: newI.append((iid, h, (z, i, d - 1)))
            elif z == o:
                if i == 0: newI.append((iid, h, (alias[0], alias[1], 0)))
                else: newI.append((iid, h, (z, i - 1, d)))
            elif s.kd(z, o): newI.append((iid, h, (z, i, d)))
            else: return None
        return Form(f1.O[:j] + f1.O[j + 1:], newI), g, oid

    def in_first(s, f, p):
        iid, h, (z, i, d) = f.I[p]
        if not all(s.kd(h, m) for _, m, _ in f.I[p + 1:]): return None
        if not all(s.kd(h, o) for _, o in f.O): return None
        for _, o in f.O[:d]:
            if o == z: i += 1
            elif not s.kd(z, o): return None
        newI = []
        for q, (jid, m, (y, k, e)) in enumerate(f.I):
            if q == p: continue
            if y == h: newI.append((jid, m, (y, k + 1, e)))
            elif s.kd(y, h): newI.append((jid, m, (y, k, e)))
            else: return None
        s.stats['moves'] += len(f.O) + len(f.I)
        return (iid, h, (z, i, 0)), Form(f.O, newI)

    def move_one(s, f1, f2, x):
        """Item x of f1 moves into f2, alone.  Returns (f1', g, cancelled, lost_input) or None."""
        for j, (oid, o) in enumerate(f1.O):
            if oid == x:
                r = s.out_first(f1, j)
                if r is None:
                    a = s.out_alias(f1, f2, j)
                    if a is None: return None
                    f1n, g, _ = a
                    for q, (iid, h, t) in enumerate(f1n.I):
                        if t[2] == j: f1n.I[q] = (iid, h, s.nread(f1n.O, t))
                    s.place_outputs(f1n, up=range(j, len(f1n.O)))
                    return f1n, g, {oid}, False, False
                item, f1n = r
                c = s.compose(Form([item], []), f2)
                if c is None: return None
                g, no, ni, canc = c
                for q, (iid, h, t) in enumerate(f1n.I):
                    if t[2] == j: f1n.I[q] = (iid, h, s.nread(f1n.O, t))
                s.place_outputs(f1n, up=range(j, len(f1n.O)))
                return f1n, g, no, canc, False
        for p, (iid, h, t) in enumerate(f1.I):
            if iid == x:
                r = s.in_first(f1, p)
                if r is None: return None
                item, f1n = r
                c = s.compose(Form([], [item]), f2)
                if c is None: return None
                g, no, ni, canc = c
                s.place_inputs(f1n, outward=range(p, len(f1n.I)))
                return f1n, g, ni, canc, True
        return None

    # ---------- the word ----------
    def settle(s, st, work):
        """work: list of (k, cands): items of st[k] (None: all) to try against st[k+1]."""
        while work:
            k, cands = work.pop()
            s.stats['visits'] += 1
            if k < 0 or k + 1 >= len(st): continue
            f1, f2 = st[k], st[k + 1]
            if not (isinstance(f1, Form) and isinstance(f2, Form)): continue
            if cands is None:
                c = s.compose(f1, f2)
                if c is not None:
                    g, no, ni, canc = c
                    st[k:k + 2] = [g] if not g.empty() else []
                    if not g.empty(): work.append((k, set(no) | set(ni)))
                    continue
                cands = f1.ids()
            moved = True
            while moved:
                moved = False
                for x in [x for x, _ in f1.O] + [x for x, _, _ in f1.I]:
                    if x not in cands: continue
                    r = s.move_one(f1, f2, x)
                    if r is None: continue
                    f1, g, new, canc, lost_in = r
                    st[k], st[k + 1] = f1, g; f2 = g; moved = True
                    work.append((k + 1, set(new)))
                    if canc: cands = f1.ids()            # an input of f2 went: anything of f1 may go now
                    if lost_in: work.append((k - 1, None))
                    break
            if f1.empty():
                del st[k]
                work.append((k - 1, None))

    def insert(s, item, st):
        if isinstance(item, Form) and item.empty(): return st
        st.insert(0, item)
        s.settle(st, [(0, None)])
        return st

    # ---------- expressions ----------
    def lift(s, h, item):
        if isinstance(item, Atom): return Atom((h,) + item.L, item.n)
        rid = next(_ids)
        f = Form([(next(_ids), h)] + item.O, [(rid, h, (h, 0, 0))] + [(i, l, (z, k, d + 1)) for (i, l, (z, k, d)) in item.I])
        s.place_inputs(f, inward=[0]); s.place_outputs(f, down=[0])
        s.absorb_new(f, {rid})
        return f

    def lift_many(s, L, item):
        """item under the lifts L, outermost first: new outputs on top, restores outside; the
        restores that can go are absorbed innermost first, then the rest are placed."""
        if isinstance(item, Atom): return Atom(tuple(L) + item.L, item.n)
        n = len(L)
        rids = [next(_ids) for _ in L]
        f = Form([(next(_ids), h) for h in L] + item.O,
                 [(rids[k], L[k], (L[k], 0, k)) for k in range(n)] + [(i, l, (z, x, d + n)) for (i, l, (z, x, d)) in item.I])
        for p in range(n - 1, -1, -1):
            s.absorb_at(f, p, lo=p)       # only inputs inside a restore read below its slot
        left = {x for x, _, _ in f.I} & set(rids)
        k = sum(1 for x, _, _ in f.I if x in left)
        s.place_inputs(f, inward=range(k - 1, -1, -1))
        s.place_outputs(f, down=range(min(k, len(f.O)) - 1, -1, -1))
        return f

    def norm(s, e, st):
        """e: ('W', h) | ('E', h, (z, i)) | ('Lift', h, e') | ('C', [e1, ..., en]) (e1 first on variables) | ('A', n)."""
        tag = e[0]
        if tag == 'W': return s.insert(Form([(next(_ids), e[1])], []), st)
        if tag == 'E': return s.insert(Form([], [(next(_ids), e[1], (e[2][0], e[2][1], 0))]), st)
        if tag == 'A': return s.insert(Atom((), e[1]), st)
        if tag == 'C':
            for x in reversed(e[1]): st = s.norm(x, st)
            return st
        if tag == 'Lift':
            L = []
            while e[0] == 'Lift': L.append(e[1]); e = e[2]      # a chain of lifts, outermost first
            w = s.norm(e, [])
            for it in reversed(w): st = s.insert(s.lift_many(L, it), st)
            return st
        raise ValueError(e)

    def run(s, e):
        st = s.norm(e, [])
        return tuple(it.key() for it in st)

# ---------- from the flat test words ----------
def lab(v, BOUND): return BOUND if v[0] == 'b' else v[1]
def idx(v): return v[1] if v[0] == 'b' else v[2]
def of_word(w, BOUND):
    out = []
    for st in w:
        if st[0] == 'W': out.append(('W', st[1]))
        elif st[0] == 'E': out.append(('E', st[1], (lab(st[2], BOUND), idx(st[2]))))
        elif st[0] == 'L': out.append(('Lift', st[1], ('W', st[2])))
    return ('C', out)
