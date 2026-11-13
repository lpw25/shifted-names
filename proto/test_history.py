import random, sys
import graph as G
from printer3 import to_expr
from printer import esize
from test_canon import rexp, rterm
from sem import meaning


def sfsize(e):  # size of a share-free expression
    return esize(e)


def op(rng, o, depth):
    c = rexp(rng, depth)          # share-free piece
    k = rng.randrange(6)
    l = rng.choice(G.LABELS)
    if k == 0: return ('comp', c, o), esize(c)
    if k == 1: return ('comp', o, c), esize(c)
    if k == 2: return ('lift', l, o), 1
    if k == 3: return ('outer', l, o), 1
    if k == 4: return ('inner', l, ('tbind', 0, ('pcomp', o, ('pid',))), c), esize(c) + 2
    return ('comp', ('lift', l, c), ('inner', l, ('tvar', l, 1), o)), esize(c) + 3


def run(seed, steps, depth, check_sem):
    rng = random.Random(seed)
    G.reset()
    e = rexp(rng, depth)
    h = sfsize(e)
    worst = (0, 0)
    for i in range(steps):
        G.EVALS[0] = 0
        r = G.graph(e)
        ev, sz = G.EVALS[0], G.size(r)
        worst = (max(worst[0], ev / h), max(worst[1], sz / h))
        o = to_expr(r)
        if check_sem and meaning(o) != meaning(e):
            print('MEANING CHANGED'); return
        e, dh = op(rng, o, depth)
        h += dh
    print('seed %d: history size %d, last graph %d, max evals/h %.2f, max graph/h %.2f' % (seed, h, sz, worst[0], worst[1]))


if __name__ == '__main__':
    for s in range(int(sys.argv[1])):
        run(s, int(sys.argv[2]), int(sys.argv[3]), len(sys.argv) > 4)
