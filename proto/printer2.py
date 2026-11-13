"""A readable linearisation: each node as  ⟦ cells | tail ⟧  (AInner chains over
one tail), sharing only nodes with two or more parents.  Deterministic in the
graph, so canonical."""
import graph as G
from graph import LABELS, OBJS


def cells_of(lr):
    """All suffixes of a list ref: [(k, suffix_ref)] with k cells before it,
    and the entries (absolute)."""
    out, ents = [(0, lr)], []
    s, oid = lr
    while OBJS[oid][0] == 'cons':
        o = OBJS[oid]
        ents.append(G.ent_shift(o[1], s))
        s, oid = G.sh_add(s, o[2][0]), o[2][1]
        out.append((len(ents), G.ref(s, oid)))
    return out, ents


def node_refs(r):
    return [G.node_list(r, l) for l in LABELS]


def reach_nodes(root):
    seen, order = set(), []

    def visit(i):
        if i in seen:
            return
        seen.add(i)
        o = OBJS[i]
        for c in kids(i):
            visit(c)
        if o[0] == 'node':
            order.append(i)
    visit(root[1])
    return order


def kids(i):
    o = OBJS[i]
    if o[0] == 'node':
        return [lr[1] for lr in o[1]]
    if o[0] == 'cons':
        return [o[2][1]] + ([o[1][3][1]] if o[1][0] in ('T', 'S') else [])
    if o[0] == 'nils':
        return [o[3][1]]
    return []


def split(r, nodes, loose=False):
    """Choose the tail of node ref r: returns (cells per label, tail) where tail is
    ('node', ref) | ('stuck', a, R, preshift) | ('id', postshift) | ('labels',).
    loose: the bound label is unobservable (a phantom payload) and may be
    printed as the tail gives it."""
    labs = [l for l in LABELS if not (loose and l == '.')]
    per = [cells_of(G.node_list(r, l)) for l in labs]
    nodes = [m for m in nodes]
    best = None
    # node tails
    for m in nodes:
        if m == r[1]:
            continue
        mls = [G.node_list((( ), m), l) for l in labs]
        s0 = None
        ks = []
        for (suf, _), ml in zip(per, mls):
            hit = None
            for k, sr in suf:
                if sr[1] == ml[1]:
                    d = dict(sr[0])
                    for l2, v in ml[0]:
                        d[l2] = d.get(l2, 0) - v
                    if any(v < 0 for v in d.values()):
                        continue
                    hit = (k, tuple(sorted((l2, v) for l2, v in d.items() if v)))
                    break
            if hit is None:
                break
            ks.append(hit[0])
            s0 = hit[1] if s0 is None else s0
            if hit[1] != s0 and G.sh_restrict(hit[1], G.outlabs(m)) != G.sh_restrict(s0, G.outlabs(m)):
                break
        else:
            cost = sum(ks)
            if best is None or cost < best[0]:
                best = (cost, ks, ('node', G.ref(s0, m)))
    # final tails: identity or stuck
    ks, kind = [], None
    for (suf, _), l in zip(per, labs):
        k, sr = suf[-1]
        o = OBJS[sr[1]]
        ks.append(k)
        if o[0] == 'nilv':
            kd = ('id',)
        else:
            kd = ('stuck', o[2], G.ref_shift(o[3], sr[0]))
        kind = kd if kind is None or kind == kd else 'mixed'
    if kind != 'mixed':
        cost = sum(ks)
        if best is None or cost < best[0]:
            if kind[0] == 'id':
                post = tuple((l, G.sh_get(per[i][0][-1][1][0], l)) for i, l in enumerate(labs))
                post = tuple((l, v) for l, v in post if v)
                best = (cost, ks, ('id', post))
            else:
                pre = tuple((l, OBJS[per[i][0][-1][1][1]][4]) for i, l in enumerate(labs))
                pre = tuple((l, v) for l, v in pre if v)
                best = (cost, ks, ('stuck', kind[1], kind[2], pre))
    if best is None:
        return None, ('labels',)
    ks = dict(zip(labs, best[1]))
    cells = [cells_of(G.node_list(r, l))[1][:ks[l]] if l in ks else [] for l in LABELS]
    return cells, best[2]


def to_expr(root):
    nodes = reach_nodes(root)
    plan = {}
    parents = {}

    strict = {root[1]}

    def deps_of(i):
        cells, tail = split(((), i), nodes, loose=i not in strict)
        plan[i] = (cells, tail)
        ds = []
        if tail[0] == 'labels':
            for l in LABELS:
                suf, ents = cells_of(G.node_list(((), i), l))
                for e in ents:
                    if e[0] in ('T', 'S'):
                        ds.append(e[3][1])
                        if not (e[0] == 'T' and e[2] is None):
                            strict.add(e[3][1])
                o = OBJS[suf[-1][1][1]]
                if o[0] == 'nils':
                    ds.append(o[3][1]); strict.add(o[3][1])
            return ds
        for cl in cells:
            for e in cl:
                if e[0] in ('T', 'S'):
                    ds.append(e[3][1])
                    if not (e[0] == 'T' and e[2] is None):
                        strict.add(e[3][1])
        if tail[0] == 'node':
            ds.append(tail[1][1]); strict.add(tail[1][1])
        if tail[0] == 'stuck':
            ds.append(tail[2][1]); strict.add(tail[2][1])
        return ds

    order, seen = [], set()

    def visit(i):
        if i in seen:
            return
        seen.add(i)
        for d in deps_of(i):
            parents[d] = parents.get(d, 0) + 1
            visit(d)
        order.append(i)
    visit(root[1])
    endid = G.end()[1]
    shared = [i for i in order if parents.get(i, 0) >= 2 and i != endid]
    names = {i: 'k%d' % n for n, i in enumerate(shared)}

    def post(e, s):
        for l, k in s:
            for _ in range(k):
                e = ('outer', l, e)
        return e

    def ref_expr(r):
        return post(obj(r[1]), r[0])

    def obj(i):
        if i == endid:
            return ('id',)
        if i in names:
            return ('ref', names[i])
        return raw(i)

    def raw(i):
        cells, tail = plan[i]
        if tail[0] == 'labels':
            return ('labels', tuple((l, lst(G.node_list(((), i), l))) for l in LABELS))
        if tail[0] == 'node':
            e = ref_expr(tail[1])
        elif tail[0] == 'id':
            e = post(('id',), tail[1])
        else:
            _, a, R, pre = tail
            e = ('comp', ref_expr(R), ('atom', a))
            for l, k in pre:
                for _ in range(k):
                    e = ('comp', e, ('outer', l, ('id',)))
        for l, cl in zip(LABELS, cells):
            for ent in reversed(cl):
                e = ('inner', l, entry(ent), e)
        return e

    def lst(lr):
        suf, ents = cells_of(lr)
        sr = suf[-1][1]
        o = OBJS[sr[1]]
        if o[0] == 'nilv':
            t = ('lof', o[1], post(('id',), sr[0]))
        else:
            _, l, a, R, m = o
            t = ('comp', ref_expr(G.ref_shift(R, sr[0])), ('atom', a))
            for _ in range(m):
                t = ('comp', t, ('outer', l, ('id',)))
            t = ('lof', l, t)
        for ent in reversed(ents):
            t = ('lcons', entry(ent), t)
        return t

    def entry(e):
        if e[0] == 'V':
            return ('tvar', e[1], e[2])
        if e[0] == 'T':
            p = ('pcomp', ref_expr(e[3]), ('patom', e[2]) if e[2] is not None else ('pid',))
            return ('tbind', e[1], p)
        _, a, z, R = e
        return ('tvia', z, ('comp', ref_expr(R), ('atom', a)))

    e = ref_expr(root)
    for i in reversed(shared):
        e = ('share', names[i], raw(i), e)
    return e
