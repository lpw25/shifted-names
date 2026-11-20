"""Stuck lookups with a memoised walk state (prototype, on hcost's lists).

In a normal word, a step after a stuck lookup of h is passed exactly when its label is known
distinct from h and sorts after every label kept so far (checked: 443,463 passed steps, no
exception).  So the rest of the walk depends only on the cell and on E, the labels of the rest that
could still pass: known distinct from h and above every kept label.  Keeping a step on y replaces E
by E n up(y).  Two memos:

  R(cell, E)   the payload from cell on      lookups whose states meet share the rest of the walk
  F(E, y)      E n up(y)                     the same filter on the same E is computed once

E is a hash-consed set.  The walk stops when no label of E occurs in the rest (the rest is kept
whole and shared).

Counts: walk (cells walked), filt (labels tested by new filters), fmemo / rmemo (memo hits),
init (labels tested to start E).

python3 hemem.py [family ...]; python3 hemem.py check
"""
import sys
import hcost
from hcost import H, FAMILIES


class HE(H):
    follow = 'emem'

    def __init__(s, facts):
        super().__init__(facts)
        s.sets = {frozenset(): 0}; s.setof = [frozenset()]
        s.fm = {}; s.rm = {}

    def sid(s, fs):
        i = s.sets.get(fs)
        if i is None: i = len(s.setof); s.sets[fs] = i; s.setof.append(fs)
        return i

    def filt(s, e, y):
        k = (e, y)
        if k in s.fm: s.C['fmemo'] += 1; return s.fm[k]
        E = s.setof[e]; s.C['filt'] += len(E)
        r = s.sid(frozenset(u for u in E if s.before(y, u)))
        s.fm[k] = r
        return r

    def follow_emem(s, h, i, w):
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
        if st[0] == 'A': return s.val(('L', h, i, c))
        rest = s.labs(nxt)
        s.C['init'] += len(rest)
        e = s.sid(frozenset(u for u in rest if s.kd(u, h) and s.before(st[1], u)))
        return s.val(('L', h, i, s.remainder(c, e, kept_first=True)))

    def remainder(s, c, e, kept_first=False):
        """The kept steps from cell c on, with E = e before c (c's own step kept when kept_first)."""
        path = []                                          # (cell, e at the cell, kept?)
        cur = c; first = kept_first
        while True:
            if cur == 1: r = 1; break
            if (cur, e, first) in s.rm: s.C['rmemo'] += 1; r = s.rm[(cur, e, first)]; break
            E = s.setof[e]
            if not first and (not E or E.isdisjoint(s.labs(cur))): r = cur; break   # all kept
            st, nxt = s.cell[cur]; s.C['walk'] += 1
            if st[0] == 'A': r = cur; break
            kept = first or st[1] not in E
            path.append((cur, e, first, kept))
            if kept: e = s.filt(e, st[1])
            cur = nxt; first = False
        for cur, e0, f0, kept in reversed(path):
            st, nxt = s.cell[cur]
            if kept: r = cur if r == nxt else s.hcons(st, r)
            s.rm[(cur, e0, f0)] = r
        return r


def check(fam, n):
    mk, facts = FAMILIES[fam]
    if facts is None: facts = getattr(hcost, mk.__name__ + '_facts')(n)
    h = HE(facts)
    HE.follow = 'coq'; a = h.norm(mk(n), 1)
    HE.follow = 'emem'; b = h.norm(mk(n), 1)
    return a == b

if __name__ == '__main__':
    sys.setrecursionlimit(200000)
    args = sys.argv[1:]
    if args and args[0] == 'check':
        for f in args[1:] or FAMILIES: print(f, [check(f, n) for n in (20, 41, 100, 203)], flush=True)
        sys.exit()
    keys = ('walk', 'filt', 'fmemo', 'rmemo', 'init', 'nstep', 'stop', 'hcons', 'stuck')
    for f in args or FAMILIES:
        mk, facts = FAMILIES[f]
        rows = []
        for n in [125, 250, 500, 1000]:
            fs = facts if facts is not None else getattr(hcost, mk.__name__ + '_facts')(n)
            h = HE(fs); HE.follow = 'emem'; h.norm(mk(n), 1)
            rows.append((n, {k: h.C[k] for k in keys}))
        print(f'{f}:')
        for key in keys:
            vals = [r[1][key] for r in rows]
            if any(vals): print(f'   {key:6s} {vals}  growth x{" x".join(hcost.growth(rows, key))}')
