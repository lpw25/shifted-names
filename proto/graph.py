"""Prototype of the canonical graph of adjustments (docs/canonical-graph.md).

Expressions (mirroring aexp/texp/pexp of Core/Normalise.v, plus share):
  ('id',) ('atom', n) ('comp', a, b) [b first, then a]
  ('outer', h, a) ('inner', h, t, a) ('lift', h, a)
  ('share', r, a, b) ('ref', r)
  terms:    ('tvar', h, i) ('tbind', u, p) ('tshift', h, t)
  payloads: ('pid',) ('patom', n) ('pcomp', a, p) [p first, then a] ('pshift', h, p)
Labels are strings; '.' is the bound label.  A fixed finite label set.
"""
import itertools

LABELS = ('.', 'x', 'y')

# ---------------------------------------------------------------- interning
TABLE = {}
OBJS = []


def intern(o):
    i = TABLE.get(o)
    if i is None:
        i = len(OBJS)
        TABLE[o] = i
        OBJS.append(o)
    return i


def reset():
    TABLE.clear()
    OBJS.clear()


# A shift is a tuple of (label, k) with k > 0, sorted.  An object id with a
# shift is a "ref": (shift, id).  Objects: lists and nodes, kept in a
# factored form where every label with outputs has minimal output index 0.

def sh_get(s, l):
    for (l2, k) in s:
        if l2 == l:
            return k
    return 0


def sh_add(s, t):
    d = dict(s)
    for l, k in t:
        d[l] = d.get(l, 0) + k
    return tuple(sorted((l, k) for l, k in d.items() if k))


def sh_sub(s, t):
    d = dict(s)
    for l, k in t:
        d[l] = d.get(l, 0) - k
        assert d[l] >= 0
    return tuple(sorted((l, k) for l, k in d.items() if k))


def sh_restrict(s, labs):
    return tuple((l, k) for l, k in s if l in labs)


def outlabs(oid):
    return OUT[oid]


OUT = {}  # object id -> frozenset of labels with outputs


def mkobj(o, labs):
    i = intern(o)
    OUT[i] = frozenset(labs)
    return i


def ref(s, oid):
    return (sh_restrict(s, outlabs(oid)), oid)


def ref_shift(r, t):
    return ref(sh_add(r[0], t), r[1])


def ref_labs(r):
    return outlabs(r[1])


# entries: ('V', l, i) | ('T', u, b, ref) | ('S', a, z, ref)   (absolute form)

def ent_min(e):
    if e[0] == 'V':
        return {e[1]: e[2]}
    r = e[3]
    return {l: sh_get(r[0], l) for l in ref_labs(r)}


def ent_sub(e, s):
    if e[0] == 'V':
        return ('V', e[1], e[2] - sh_get(s, e[1]))
    r = e[3]
    return e[:3] + ((sh_sub(r[0], sh_restrict(s, ref_labs(r))), r[1]),)


def ent_shift(e, s):
    if e[0] == 'V':
        return ('V', e[1], e[2] + sh_get(s, e[1]))
    return e[:3] + (ref_shift(e[3], s),)


def factor(mins):
    """mins: list of dicts label->min.  Returns shift."""
    d = {}
    for m in mins:
        for l, k in m.items():
            d[l] = min(d.get(l, k), k)
    return tuple(sorted((l, k) for l, k in d.items() if k))


def ref_min(r):
    return {l: sh_get(r[0], l) for l in ref_labs(r)}


# lists for label l:
#   ('nilv', l)                     j -> V(l, j)
#   ('nils', l, a, R, m)            j -> S(a, (l, j+m), R)
#   ('cons', e, tailref)

def nilv(l):
    return ref((), mkobj(('nilv', l), {l}))


def nils(l, a, R, m):
    s = factor([ref_min(R)])
    R0 = (sh_sub(R[0], s), R[1])
    return ref(s, mkobj(('nils', l, a, R0, m), ref_labs(R)))


def lst_label(oid):
    o = OBJS[oid]
    if o[0] in ('nilv', 'nils', 'nilp'):
        return o[1]
    return o[3]


def cons(l, e, tail):
    """The list for label l: e, then tail (a list ref)."""
    to = OBJS[tail[1]]
    # absorb into a nil
    if to[0] == 'nilv':
        k = sh_get(tail[0], l)
        if k >= 1 and e == ('V', l, k - 1):
            return ref(sh_sub(tail[0], ((l, 1),)), tail[1])
    if to[0] == 'nils':
        _, _, a, R, m = to
        if m >= 1 and e == ('S', a, (l, m - 1), ref_shift(R, tail[0])):
            return nils(l, a, ref_shift(R, tail[0]), m - 1)
    s = factor([ent_min(e), ref_min(tail)])
    e0 = ent_sub(e, s)
    t0 = (sh_sub(tail[0], sh_restrict(s, ref_labs(tail))), tail[1])
    labs = set(ent_min(e)) | set(ref_labs(tail))
    return ref(s, mkobj(('cons', e0, t0, l), labs))


def lookup(lr, i):
    """Entry at index i of list ref lr (absolute)."""
    s, oid = lr
    o = OBJS[oid]
    while o[0] == 'cons' and i > 0:
        s = sh_add(s, o[2][0])
        oid = o[2][1]
        o = OBJS[oid]
        i -= 1
    if o[0] == 'cons':
        return ent_shift(o[1], s)
    if o[0] in ('nilv', 'nilp'):
        return ('V', o[1], i + sh_get(s, o[1]))
    _, l, a, R, m = o
    return ('S', a, (l, i + m), ref_shift(R, s))


def drop(lr):
    s, oid = lr
    o = OBJS[oid]
    if o[0] == 'nilp':
        return lr
    if o[0] == 'cons':
        return ref(sh_add(s, o[2][0]), o[2][1])
    if o[0] == 'nilv':
        return ref(sh_add(s, ((o[1], 1),)), oid)
    _, l, a, R, m = o
    return nils(l, a, ref_shift(R, s), m + 1)


# nodes: ('node', (listref per label in LABELS))

def node(lists):
    s = factor([ref_min(lr) for lr in lists])
    ls = tuple((sh_sub(lr[0], sh_restrict(s, ref_labs(lr))), lr[1]) for lr in lists)
    labs = set()
    for lr in lists:
        labs |= ref_labs(lr)
    return ref(s, mkobj(('node', ls), labs))


def node_list(r, l):
    s, oid = r
    lr = OBJS[oid][1][LABELS.index(l)]
    return ref_shift(lr, s)


def apply(r, v):
    l, i = v
    return lookup(node_list(r, l), i)


END = None


def end():
    return node([nilv(l) for l in LABELS])


def preshift(h, K):
    return node([drop(node_list(K, l)) if l == h else node_list(K, l) for l in LABELS])


def phantom(k):
    """A payload without payload atom: only named inputs are observed.  The
    bound inputs are sent to bound outputs from the least bound output of
    the named part on, so the choice commutes with shifts."""
    return node([nilp() if l == '.' else node_list(k, l) for l in LABELS])


def nilp():
    """The bound inputs of a payload without payload atom: not observable.
    No outputs, so it commutes with every shift."""
    return ref((), mkobj(('nilp', '.'), set()))


# ---------------------------------------------------------------- evaluation
MEMO = {}
EVALS = [0]


def ev(a, K, env):
    """a, then K.  Memoised on the core of K: a, then K, then a shift, is
    (a, then K), then the shift."""
    s, n = K
    key = (id(a), n, envkey(env))
    if key not in MEMO:
        EVALS[0] += 1
        MEMO[key] = ev0(a, ((), n), env)
    return ref_shift(MEMO[key], s)


def envkey(env):
    return tuple(sorted((r, id(v[0])) for r, v in env.items()))


def ev0(a, K, env):
    tag = a[0]
    if tag == 'id':
        return K
    if tag == 'atom':
        return node([nils(l, a[1], K, 0) for l in LABELS])
    if tag == 'comp':
        return ev(a[2], ev(a[1], K, env), env)
    if tag == 'outer':
        return ev(a[2], preshift(a[1], K), env)
    if tag == 'inner':
        h, t, b = a[1], a[2], a[3]
        e = evt(t, K, env)
        B = ev(b, K, env)
        return node([cons(h, e, node_list(B, l)) if l == h else node_list(B, l) for l in LABELS])
    if tag == 'lift':
        h, b = a[1], a[2]
        e = apply(K, (h, 0))
        B = ev(b, preshift(h, K), env)
        return node([cons(h, e, node_list(B, l)) if l == h else node_list(B, l) for l in LABELS])
    if tag == 'share':
        env2 = dict(env)
        env2[a[1]] = (a[2], env)
        return ev(a[3], K, env2)
    if tag == 'ref':
        b, benv = env[a[1]]
        return ev(b, K, benv)
    if tag == 'labels':
        d = dict(a[1])
        return node([evl(d[l], K, env, l) for l in LABELS])
    raise ValueError(a)


def evl(L, K, env, l):
    """A list expression for label l, then K."""
    if L[0] == 'lcons':
        return cons(l, evt(L[1], K, env), evl(L[2], K, env, l))
    if L[0] == 'lof':
        return node_list(ev(L[2], K, env), L[1])
    raise ValueError(L)


def tvarof(t):
    if t[0] == 'tvar':
        return (t[1], t[2])
    if t[0] == 'tshift':
        w = tvarof(t[2])
        if w is None:
            return None
        h = t[1]
        return (w[0], w[1] + 1) if w[0] == h else w
    return None


def evt(t, K, env):
    if t[0] == 'tvia':
        return apply(ev(t[2], K, env), t[1])
    w = tvarof(t)
    if w is not None:
        return apply(K, w)
    while t[0] == 'tshift':
        t = t[2]
    u, p = t[1], t[2]
    b, k = evp(p, K, env)
    if b is None:
        k = phantom(k)
    return ('T', u, b, k)


def evp(p, K, env):
    tag = p[0]
    if tag == 'pid':
        return None, K
    if tag == 'patom':
        return p[1], K
    if tag == 'pcomp':
        return evp(p[2], ev(p[1], K, env), env)
    if tag == 'pshift':
        return evp(p[2], preshift(p[1], K), env)
    raise ValueError(p)


def graph(a):
    MEMO.clear()
    return ev(a, end(), {})


def size(r):
    """Number of distinct objects reachable from r."""
    seen = set()
    stack = [r[1]]
    while stack:
        i = stack.pop()
        if i in seen:
            continue
        seen.add(i)
        o = OBJS[i]
        if o[0] == 'node':
            stack.extend(lr[1] for lr in o[1])
        elif o[0] == 'cons':
            stack.append(o[2][1])
            if o[1][0] in ('T', 'S'):
                stack.append(o[1][3][1])
        elif o[0] == 'nils':
            stack.append(o[3][1])
    return len(seen)
