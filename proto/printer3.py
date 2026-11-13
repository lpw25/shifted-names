"""Readable, linear linearisation.  A node is printed as  ⟦ cells | tail ⟧
when it has a common tail and none of the cells it strips is shared;
otherwise label by label, naming shared lists.  Objects referenced twice or
more in the chosen forms are shared.  Deterministic in the graph."""
import sys
import graph as G
from graph import LABELS, OBJS

sys.setrecursionlimit(100000)


def kids(i):
    o = OBJS[i]
    if o[0] == 'node':
        return [lr[1] for lr in o[1]]
    if o[0] == 'cons':
        return [o[2][1]] + ([o[1][3][1]] if o[1][0] in ('T', 'S') else [])
    if o[0] == 'nils':
        return [o[3][1]]
    return []


def raw_parents(root):
    par, seen, stack = {}, set(), [root]
    while stack:
        i = stack.pop()
        if i in seen:
            continue
        seen.add(i)
        for c in kids(i):
            par[c] = par.get(c, 0) + 1
            stack.append(c)
    return par, seen


def walk(lr):
    """[(cells_before, suffix_ref)], entries, cell objects."""
    out, ents, objs = [(0, lr)], [], []
    s, oid = lr
    while OBJS[oid][0] == 'cons':
        o = OBJS[oid]
        objs.append(oid)
        ents.append(G.ent_shift(o[1], s))
        s, oid = G.sh_add(s, o[2][0]), o[2][1]
        out.append((len(ents), G.ref(s, oid)))
    return out, ents, objs


def match_shift(sr, ml):
    """s with ref_shift(ml, s) == sr on sr's output labels, or None."""
    if sr[1] != ml[1]:
        return None
    d = {}
    for l in G.outlabs(sr[1]):
        v = G.sh_get(sr[0], l) - G.sh_get(ml[0], l)
        if v < 0:
            return None
        d[l] = v
    return d


def merge(a, b):
    for l, v in b.items():
        if a.get(l, v) != v:
            return None
        a[l] = v
    return a


def to_expr(root):
    par, reach = raw_parents(root[1])
    nodes = sorted(i for i in reach if OBJS[i][0] == 'node')
    endid = G.end()[1]
    listnode = {}
    for m in nodes:
        for l in LABELS:
            t, oid = G.node_list(((), m), l)
            listnode.setdefault(oid, (m, t))

    def via_node(oid, s):
        """A shared list object as the list of a node: (node, postshift) or None."""
        if oid not in listnode:
            return None
        m, t = listnode[oid]
        d = {}
        for l in G.outlabs(oid):
            v = G.sh_get(s, l) - G.sh_get(t, l)
            if v < 0:
                return None
            d[l] = v
        return m, tuple(sorted((l, v) for l, v in d.items() if v))
    form = {}

    desc_memo = {}

    def desc(i):
        if i not in desc_memo:
            out, stack = set(), list(kids(i))
            while stack:
                j = stack.pop()
                if j in out:
                    continue
                out.add(j)
                stack.extend(kids(j))
            desc_memo[i] = out
        return desc_memo[i]

    def choose(i, loose):
        r = ((), i)
        below = desc(i)
        labs = [l for l in LABELS if not (loose and l == '.')]
        walks = {l: walk(G.node_list(r, l)) for l in labs}
        best = None

        def ok(l, k):
            return all(par.get(c, 0) <= 1 for c in walks[l][2][1:k]) and (k == 0 or par.get(walks[l][2][0], 0) <= 1)

        for m in nodes:
            if m == i or m not in below:
                continue
            s, ks = {}, {}
            for l in labs:
                ml = G.node_list(((), m), l)
                hit = None
                for k, sr in walks[l][0]:
                    d = match_shift(sr, ml)
                    if d is not None:
                        hit = (k, d)
                        break
                if hit is None or not ok(l, hit[0]) or merge(s, hit[1]) is None:
                    break
                ks[l] = hit[0]
            else:
                cost = sum(ks.values())
                if best is None or cost < best[0]:
                    best = (cost, ks, ('node', G.ref(tuple(sorted((l, v) for l, v in s.items() if v)), m)))
        kind, ks, post, pre = None, {}, {}, {}
        for l in labs:
            k, sr = walks[l][0][-1]
            o = OBJS[sr[1]]
            ks[l] = k
            if not ok(l, k):
                kind = 'mixed'
            if o[0] == 'nilv':
                kd = ('id',)
                post[l] = G.sh_get(sr[0], l)
            else:
                kd = ('stuck', o[2], G.ref_shift(o[3], sr[0]))
                pre[l] = o[4]
            kind = kd if kind is None or kind == kd else 'mixed'
        if kind != 'mixed':
            cost = sum(ks.values())
            if best is None or cost < best[0]:
                if kind[0] == 'id':
                    best = (cost, ks, ('id', tuple((l, v) for l, v in sorted(post.items()) if v)))
                else:
                    best = (cost, ks, ('stuck', kind[1], kind[2], tuple((l, v) for l, v in sorted(pre.items()) if v)))
        if best is None:
            return ('labels',)
        cells = {l: walks[l][1][:best[1][l]] for l in labs}
        return ('cf', cells, best[2])

    # pass 1: choose forms, count references
    refs = {}
    strict = set([root[1]])
    todo = [root[1]]
    loose_of = {}

    def ref_obj(i, is_strict):
        refs[i] = refs.get(i, 0) + 1
        if is_strict:
            strict.add(i)
        todo.append(i)

    def entry_refs(e):
        if e[0] in ('T', 'S'):
            ref_obj(e[3][1], not (e[0] == 'T' and e[2] is None))

    def list_refs(lr, first):
        """References made by printing list lr inline (cells until a shared one)."""
        s, oid = lr
        while True:
            o = OBJS[oid]
            if not first and par.get(oid, 0) >= 2 and o[0] == 'cons':
                vn = via_node(oid, s)
                ref_obj(vn[0] if vn else oid, True)
                return
            first = False
            if o[0] == 'cons':
                entry_refs(o[1])
                s, oid = G.sh_add(s, o[2][0]), o[2][1]
                continue
            if o[0] == 'nils':
                ref_obj(o[3][1], True)
            return

    done = set()
    while todo:
        i = todo.pop()
        if i in done or i == endid:
            continue
        o = OBJS[i]
        if o[0] != 'node':
            done.add(i)
            list_refs(((), i), True)
            continue
        # decide after all strictness is known: choose loose only if never strict
        done.add(i)
        f = choose(i, loose=i not in strict or OBJS[OBJS[i][1][0][1]][0] == 'nilp')
        form[i] = f
        if f[0] == 'labels':
            for l in LABELS:
                list_refs(G.node_list(((), i), l), True)
        else:
            for l, cl in f[1].items():
                for e in cl:
                    entry_refs(e)
            t = f[2]
            if t[0] == 'node':
                ref_obj(t[1][1], True)
            if t[0] == 'stuck':
                ref_obj(t[2][1], True)

    # pass 2: print
    order = []
    seen = set()

    def deps(i):
        if i == endid:
            return []
        out = []
        o = OBJS[i]
        if o[0] == 'node' and form[i][0] == 'cf':
            f = form[i]
            for l, cl in f[1].items():
                out += [e[3][1] for e in cl if e[0] in ('T', 'S')]
            t = f[2]
            if t[0] == 'node':
                out.append(t[1][1])
            if t[0] == 'stuck':
                out.append(t[2][1])
            return out
        lists = [G.node_list(((), i), l) for l in LABELS] if o[0] == 'node' else [((), i)]
        for lr in lists:
            s, oid = lr
            first = True
            while True:
                oo = OBJS[oid]
                if oo[0] == 'cons' and not first:
                    pass
                if not first and par.get(oid, 0) >= 2 and oo[0] == 'cons':
                    vn = via_node(oid, s)
                    out.append(vn[0] if vn else oid)
                    break
                first = False
                if oo[0] == 'cons':
                    if oo[1][0] in ('T', 'S'):
                        out.append(oo[1][3][1])
                    s, oid = G.sh_add(s, oo[2][0]), oo[2][1]
                    continue
                if oo[0] == 'nils':
                    out.append(oo[3][1])
                break
        return out

    def visit(i):
        if i in seen:
            return
        seen.add(i)
        for d in deps(i):
            visit(d)
        order.append(i)
    visit(root[1])
    shared = [i for i in order if refs.get(i, 0) >= 2 and i != endid]
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
        o = OBJS[i]
        if o[0] != 'node':
            l = G.lst_label(i)
            return ('labels', tuple((l2, lst(((), i), True) if l2 == l else ('lof', l2, ('id',))) for l2 in LABELS))
        f = form[i]
        if f[0] == 'labels':
            return ('labels', tuple((l, lst(G.node_list(((), i), l), True)) for l in LABELS))
        cells, tail = f[1], f[2]
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
        for l in LABELS:
            for ent in reversed(cells.get(l, [])):
                e = ('inner', l, entry(ent), e)
        return e

    def lst(lr, first):
        s, oid = lr
        o = OBJS[oid]
        if not first and par.get(oid, 0) >= 2 and o[0] == 'cons':
            vn = via_node(oid, s)
            if vn:
                return ('lof', G.lst_label(oid), post(obj(vn[0]), vn[1]))
            return ('lof', G.lst_label(oid), post(obj(oid), s))
        if o[0] in ('nilv', 'nilp'):
            return ('lof', o[1], post(('id',), s))
        if o[0] == 'nils':
            _, l, a, R, m = o
            t = ('comp', ref_expr(G.ref_shift(R, s)), ('atom', a))
            for _ in range(m):
                t = ('comp', t, ('outer', l, ('id',)))
            return ('lof', l, t)
        return ('lcons', entry(G.ent_shift(o[1], s)), lst(G.ref(G.sh_add(s, o[2][0]), o[2][1]), False))

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
