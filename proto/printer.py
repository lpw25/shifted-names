"""Linearisation: the graph back to an expression, with a share for every
object (node or list) that has two or more parents."""
import graph as G
from graph import LABELS, OBJS


def children(oid):
    o = OBJS[oid]
    out = []
    if o[0] == 'node':
        out = [lr[1] for lr in o[1]]
    elif o[0] == 'cons':
        out = [o[2][1]] + ([o[1][3][1]] if o[1][0] in ('T', 'S') else [])
    elif o[0] == 'nils':
        out = [o[3][1]]
    return out


def postshift(e, s):
    for l, k in s:
        for _ in range(k):
            e = ('outer', l, e)
    return e


def preshift_id(l, m):
    e = ('id',)
    for _ in range(m):
        e = ('outer', l, e)
    return e


def to_expr(root):
    # count parents
    parents = {}
    order = []
    seen = set()

    def visit(i):
        if i in seen:
            return
        seen.add(i)
        for c in children(i):
            parents[c] = parents.get(c, 0) + 1
            visit(c)
        order.append(i)          # post-order: children first

    visit(root[1])
    shared = [i for i in order if parents.get(i, 0) >= 2]
    names = {i: 's%d' % i for i in shared}

    def node_of_list(i):
        """A node whose label-l list is the list object i (other labels identity)."""
        l = G.lst_label(i)
        return ('labels', tuple((l2, lst(i) if l2 == l else ('lof', l2, ('id',))) for l2 in LABELS))

    def obj(i):
        """The object as an adjustment (a list as a node)."""
        if i in names:
            return ('ref', names[i])
        return raw(i)

    def raw(i):
        o = OBJS[i]
        if o[0] == 'node':
            return ('labels', tuple((l, lref(lr, l)) for l, lr in zip(LABELS, o[1])))
        return node_of_list_raw(i)

    def node_of_list_raw(i):
        l = G.lst_label(i)
        return ('labels', tuple((l2, lraw(i) if l2 == l else ('lof', l2, ('id',))) for l2 in LABELS))

    def lref(lr, l):
        s, i = lr
        if not s:
            return lst(i)
        return ('lof', l, postshift(obj(i), s))

    def lst(i):
        if i in names:
            return ('lof', G.lst_label(i), ('ref', names[i]))
        return lraw(i)

    def lraw(i):
        o = OBJS[i]
        if o[0] in ('nilv', 'nilp'):
            return ('lof', o[1], ('id',))
        if o[0] == 'nils':
            _, l, a, R, m = o
            return ('lof', l, ('comp', ('comp', ref_expr(R), ('atom', a)), preshift_id(l, m)))
        _, e, t, l = o
        return ('lcons', entry(e), lref(t, l))

    def ref_expr(r):
        return postshift(obj(r[1]), r[0])

    def entry(e):
        if e[0] == 'V':
            return ('tvar', e[1], e[2])
        if e[0] == 'T':
            p = ('pcomp', ref_expr(e[3]), ('patom', e[2]) if e[2] is not None else ('pid',))
            return ('tbind', e[1], p)
        _, a, z, R = e
        return ('tvia', z, ('comp', ref_expr(R), ('atom', a)))

    body = ref_expr(root)
    for i in reversed(shared):     # outermost binding binds the latest in post-order
        pass
    # bind in post-order (children first), innermost body last
    e = body
    for i in reversed(shared):
        e = ('share', names[i], raw(i), e)
    return e


def esize(e):
    if isinstance(e, tuple):
        return 1 + sum(esize(x) for x in e[1:] if isinstance(x, tuple))
    return 0
