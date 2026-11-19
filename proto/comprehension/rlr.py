"""The context-form pass processed left to right (prototype).

Each new item is appended on the right of the settled word, and the items of
its left neighbour move into it ([settle] from rforms.py, which also looks
again further left when a form loses an input).  Stage 1: the forms and
steps of rforms.py, only the order of processing changed.

Finding: not canonical (rforms_check with this pass: 20 and 48 split classes
on the first two test sets).  E.g. in  Eg(g0) Wk Wh  the read of g stays below
h after k is placed above h, although g < h lets it move up: reads are only
taken as early as they go when they are new, so rforms.py's forms depend on
the order in which they are built.
"""
import itertools
from rforms import R, Form, Atom, _ids

class RLR(R):
    def push(s, item, st):
        if isinstance(item, Form) and item.empty(): return st
        st.append(item)
        s.settle(st, [(len(st) - 2, None)])
        return st

    def norm(s, e, st):
        tag = e[0]
        if tag == 'W': return s.push(Form([(next(_ids), e[1])], []), st)
        if tag == 'E': return s.push(Form([], [(next(_ids), e[1], (e[2][0], e[2][1], 0))]), st)
        if tag == 'A': return s.push(Atom((), e[1]), st)
        if tag == 'C':
            for x in e[1]: st = s.norm(x, st)
            return st
        if tag == 'Lift':
            L = []
            while e[0] == 'Lift': L.append(e[1]); e = e[2]
            w = s.norm(e, [])
            for it in w: st = s.push(s.lift_many(L, it), st)
            return st
        raise ValueError(e)
