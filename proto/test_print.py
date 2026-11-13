import random, sys
import graph as G
from printer3 import to_expr
from printer import esize
from sem import meaning
from test_canon import rexp
import test_size as T


def check(seed, count, depth):
    rng = random.Random(seed)
    G.reset()
    bad = 0
    for _ in range(count):
        a = rexp(rng, depth)
        r = G.graph(a)
        o = to_expr(r)
        r2 = G.graph(o)
        if r2 != r or meaning(o) != meaning(a):
            print('ROUNDTRIP FAIL', a, '\n ->', o); bad += 1
            if bad > 2: return
    print('roundtrip ok', count)


def grow(name, f, ns, c):
    for n in ns:
        G.reset()
        r = G.graph(f(n))
        o = to_expr(r)
        G.EVALS[0] = 0
        r2 = G.graph(('comp', c, o))
        print(name, 'n=%d graph=%d printed=%d | out∘c graph=%d evals=%d' % (n, G.size(r), esize(o), G.size(r2), G.EVALS[0]))


if __name__ == '__main__':
    check(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
    grow('chain', T.chain, [20, 40, 80], T.c_hard)
    grow('lifts', T.lifts, [20, 40, 80], T.c_hard)
    grow('deep', T.deep, [10, 20, 40], T.c_hard)
