import random, sys
import graph as G
from sem import meaning, probes, observe

LAB = G.LABELS


def rlab(rng):
    return rng.choice(LAB)


def rexp(rng, d, vars_=()):
    if d == 0:
        c = rng.random()
        if vars_ and c < 0.3:
            return ('ref', rng.choice(vars_))
        return ('id',) if c < 0.6 else ('atom', rng.randrange(2))
    c = rng.randrange(7)
    if c == 0:
        return ('comp', rexp(rng, d - 1, vars_), rexp(rng, d - 1, vars_))
    if c == 1:
        return ('outer', rlab(rng), rexp(rng, d - 1, vars_))
    if c == 2:
        return ('inner', rlab(rng), rterm(rng, d - 1, vars_), rexp(rng, d - 1, vars_))
    if c == 3:
        return ('lift', rlab(rng), rexp(rng, d - 1, vars_))
    if c == 4:
        r = 'r%d' % len(vars_)
        return ('share', r, rexp(rng, d - 1, vars_), rexp(rng, d - 1, vars_ + (r,)))
    return rexp(rng, d - 1, vars_) if c == 5 else ('atom', rng.randrange(2))


def rterm(rng, d, vars_):
    c = rng.randrange(3)
    if c == 0:
        return ('tvar', rlab(rng), rng.randrange(3))
    if c == 1:
        return ('tshift', rlab(rng), rterm(rng, max(d - 1, 0), vars_))
    return ('tbind', rng.randrange(2), rpay(rng, d, vars_))


def rpay(rng, d, vars_):
    if d == 0:
        return ('pid',) if rng.random() < 0.7 else ('patom', 0)
    c = rng.randrange(4)
    if c == 0:
        return ('pid',)
    if c == 1:
        return ('patom', 0)
    if c == 2:
        return ('pcomp', rexp(rng, d - 1, vars_), rpay(rng, d - 1, vars_))
    return ('pshift', rlab(rng), rpay(rng, d - 1, vars_))


def gmeaning(r, n=6, depth=4):
    """Observe the graph like the reference semantics, through G.apply."""
    def k_of(rr):
        return lambda v: conv(G.apply(rr, v))

    def conv(e):
        if e[0] == 'V':
            return e
        return e[:3] + (k_of(e[3]),)

    ps = probes(n)
    return tuple(observe(conv(G.apply(r, v)), ps, depth) for v in ps)


def main(seed, count, depth):
    rng = random.Random(seed)
    G.reset(); G.MEMO.clear()
    by_sem, by_graph = {}, {}
    bad = 0
    for _ in range(count):
        a = rexp(rng, depth)
        m = meaning(a)
        r = G.graph(a)
        if gmeaning(r) != m:
            print('UNSOUND', a); bad += 1
            if bad > 3: return
        by_sem.setdefault(m, set()).add(r)
        by_graph.setdefault(r, set()).add(m)
    noncanon = [s for s, rs in by_sem.items() if len(rs) > 1]
    print('exprs', count, 'meanings', len(by_sem), 'graphs', len(by_graph),
          'non-canonical meanings', len(noncanon))
    for s in noncanon[:2]:
        print(' graphs for one meaning:', by_sem[s])


if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
