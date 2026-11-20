"""Payloads of stuck lookups from cones memoised per (label, cell) (prototype, on hcost's lists).

K(x, c): the steps of the word c that a step on x placed in front of c reaches through dependence
(two labels are dependent when not known distinct, so a label is dependent on itself).  With t the
first step of c on a label dependent on x (nextdep, memoised per (x, cell)):

    K(x, c) = {}                                   if there is none
            = {t} u K(label t, after t) u K(x, after t)
            = every step from t on                 if t is an atom

The payload of a lookup of h stuck at the cell c is the word of the steps K(h, c), in order.  K is
memoised per (label, cell) and the sets are hash-consed, so a union of equal sets is free and
lookups stuck at different cells of the same tail share their work.

A cone is stored as a cell from which every step to the end is in it, and the cells before that
one explicitly, so a cone that is a whole suffix costs nothing to build or merge.

Counts: kent (K entries computed), union (explicit cells merged, the smaller side, as a merge of
hash-consed tries would), absorb (explicit cells absorbed into the whole suffix), nd (cells walked
by nextdep), pword (cells rebuilt for payload words).

python3 hcone.py [family ...]   counts; python3 hcone.py check   compare with hcost (follow='coq')
"""
import sys
import hcost
from hcost import H, FAMILIES


class HC(H):
    follow = 'cone'

    def __init__(s, facts):
        super().__init__(facts)
        s.sets = {(frozenset(), 1): 0}; s.setof = [(frozenset(), 1)]
        s.kmemo = {}; s.umemo = {}; s.ndmemo = {}; s.depthm = {1: 0}; s.wmemo = {0: 1}; s.allm = {}

    def depth(s, c):
        todo = []
        while c not in s.depthm: todo.append(c); c = s.cell[c][1]
        for x in reversed(todo): s.depthm[x] = s.depthm[s.cell[x][1]] + 1
        return s.depthm[c if not todo else todo[0]]

    # A cone is (E, tail): every cell from tail to the end (tail 1: none), and the cells E before
    # it.  Canonical: the cell just before tail is never in E.
    def sid(s, E, tail):
        E = frozenset(e for e in E if s.depth(e) > s.depth(tail))
        moved = True
        while moved:                                       # absorb cells that extend the tail
            moved = False
            for e in E:
                if s.cell[e][1] == tail: E = E - {e}; tail = e; moved = True; s.C['absorb'] += 1; break
        k = (E, tail); i = s.sets.get(k)
        if i is None: i = len(s.setof); s.sets[k] = i; s.setof.append(k)
        return i
    def union(s, a, b):
        if a == b or not b: return a
        if not a: return b
        k = (a, b) if a < b else (b, a)
        r = s.umemo.get(k)
        if r is None:
            (EA, ta), (EB, tb) = s.setof[a], s.setof[b]
            s.C['union'] += min(len(EA), len(EB))
            tail = ta if s.depth(ta) >= s.depth(tb) else tb
            r = s.sid(EA | EB, tail); s.umemo[k] = r
        return r

    def nextdep(s, x, c):
        """The first cell of c on a label dependent on x (not known distinct), or an atom; 1 if none."""
        path = []
        while True:
            if c == 1 or (x, c) in s.ndmemo: r = 1 if c == 1 else s.ndmemo[(x, c)]; break
            st, w = s.cell[c]; s.C['nd'] += 1
            if st[0] == 'A' or not s.kd(x, st[1]): r = c; break
            path.append(c); c = w
        for p in path: s.ndmemo[(x, p)] = r
        if c != 1: s.ndmemo[(x, c)] = r
        return r

    def allfrom(s, c): return s.sid(frozenset(), c)

    def K(s, x, c):
        # iterative over the chain of x-dependent steps, to keep Python's stack small
        chain = []
        while True:
            t = s.nextdep(x, c)
            if t == 1: r = 0; break
            if (x, t) in s.kmemo: r = s.kmemo[(x, t)]; break
            st, after = s.cell[t]
            if st[0] == 'A': r = s.allfrom(t); s.kmemo[(x, t)] = r; break
            chain.append(t); c = after
        for t in reversed(chain):
            st, after = s.cell[t]
            s.C['kent'] += 1
            own = s.union(s.sid(frozenset([t]), 1), s.K(st[1], after))
            r = s.union(own, r)
            s.kmemo[(x, t)] = r
        return r

    def word(s, k):
        """The payload word of the cone k: its explicit cells rebuilt, in order, on its tail."""
        if k in s.wmemo: return s.wmemo[k]
        E, w = s.setof[k]
        for c in sorted(E, key=s.depth):
            s.C['pword'] += 1; w = s.hcons(s.cell[c][0], w)
        s.wmemo[k] = w
        return w

    def follow_cone(s, h, i, w):
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
        s.C['stuck'] += 1
        return s.val(('L', h, i, s.word(s.K(h, c))))


def check(fam, n):
    mk, _ = FAMILIES[fam]
    facts = FAMILIES[fam][1]
    if facts is None: facts = getattr(hcost, mk.__name__ + '_facts')(n)
    h = HC(facts)
    HC.follow = 'coq'; a = h.norm(mk(n), 1)
    HC.follow = 'cone'; b = h.norm(mk(n), 1)
    return a == b

if __name__ == '__main__':
    sys.setrecursionlimit(200000)
    args = sys.argv[1:]
    if args and args[0] == 'check':
        for f in args[1:] or FAMILIES: print(f, [check(f, n) for n in (20, 41, 100, 203)])
        sys.exit()
    keys = ('kent', 'union', 'absorb', 'nd', 'pword', 'nstep', 'stop', 'hcons', 'stuck')
    for f in args or FAMILIES:
        mk, facts = FAMILIES[f]
        rows = []
        for n in [125, 250, 500, 1000]:
            fs = facts if facts is not None else getattr(hcost, mk.__name__ + '_facts')(n)
            h = HC(fs); HC.follow = 'cone'; h.norm(mk(n), 1)
            rows.append((n, {k: h.C[k] for k in keys}))
        print(f'{f}:')
        for key in keys:
            vals = [r[1][key] for r in rows]
            if any(vals): print(f'   {key:6s} {vals}  growth x{" x".join(hcost.growth(rows, key))}')
