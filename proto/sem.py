"""Reference semantics: the free model (Unique.fres) as closures, observed on probes."""
from graph import LABELS


def shift(h, v):
    return (v[0], v[1] + 1) if v[0] == h else v


def unshift(h, v):
    return (v[0], v[1] - 1) if v[0] == h and v[1] > 0 else v


def ident(v):
    return ('V',) + v


def sem(a, K, env):
    tag = a[0]
    if tag == 'id':
        return K
    if tag == 'atom':
        return lambda v: ('S', a[1], v, K)
    if tag == 'comp':
        return sem(a[2], sem(a[1], K, env), env)
    if tag == 'outer':
        h = a[1]
        return sem(a[2], lambda y: K(shift(h, y)), env)
    if tag == 'inner':
        h, t, b = a[1], a[2], a[3]
        B = sem(b, K, env)
        return lambda v: semt(t, K, env) if v == (h, 0) else B(unshift(h, v))
    if tag == 'lift':
        h, b = a[1], a[2]
        B = sem(b, lambda y: K(shift(h, y)), env)
        return lambda v: K((h, 0)) if v == (h, 0) else B(unshift(h, v))
    if tag == 'share':
        env2 = dict(env)
        env2[a[1]] = (a[2], env)
        return sem(a[3], K, env2)
    if tag == 'ref':
        b, benv = env[a[1]]
        return sem(b, K, benv)
    if tag == 'labels':
        d = dict(a[1])
        fs = {l: seml(d[l], K, env, l) for l in LABELS}
        return lambda v: fs[v[0]](v[1])
    raise ValueError(a)


def seml(L, K, env, l):
    if L[0] == 'lcons':
        rest = seml(L[2], K, env, l)
        return lambda j: semt(L[1], K, env) if j == 0 else rest(j - 1)
    if L[0] == 'lof':
        f = sem(L[2], K, env)
        return lambda j: f((L[1], j))
    raise ValueError(L)


def tvarof(t):
    if t[0] == 'tvar':
        return (t[1], t[2])
    if t[0] == 'tshift':
        w = tvarof(t[2])
        return None if w is None else shift(t[1], w)
    return None


def semt(t, K, env):
    if t[0] == 'tvia':
        return sem(t[2], K, env)(t[1])
    w = tvarof(t)
    if w is not None:
        return K(w)
    while t[0] == 'tshift':
        t = t[2]
    b, k = semp(t[2], K, env)
    return ('T', t[1], b, k)


def semp(p, K, env):
    tag = p[0]
    if tag == 'pid':
        return None, K
    if tag == 'patom':
        return p[1], K
    if tag == 'pcomp':
        return semp(p[2], sem(p[1], K, env), env)
    if tag == 'pshift':
        h = p[1]
        return semp(p[2], lambda y: K(shift(h, y)), env)
    raise ValueError(p)


def observe(res, probes, depth):
    if res[0] == 'V':
        return res
    if depth == 0:
        return res[:3] if res[0] == 'S' else res[:3]
    k = res[3]
    if res[0] == 'T':
        ps = [v for v in probes if res[2] is not None or v[0] != '.']
    else:
        ps = probes
    return res[:3] + (tuple(observe(k(v), probes, depth - 1) for v in ps),)


def probes(n):
    return [(l, i) for l in LABELS for i in range(n)]


def meaning(a, n=6, depth=4):
    f = sem(a, ident, {})
    ps = probes(n)
    return tuple(observe(f(v), ps, depth) for v in ps)
