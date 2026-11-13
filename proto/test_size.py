import graph as G

U = lambda u=0, p=('pid',): ('tbind', u, p)


def chain(L):  # ⟦x := u_i⟧ ∘ ... (no share)
    e = ('id',)
    for i in range(L):
        e = ('comp', ('inner', 'x', U(i % 2), ('id',)), e)
    return e


def lifts(L):  # (⟦x | a⟧)^L ∘ ⟦x := u⟧, the substitution first
    e = ('inner', 'x', U(), ('id',))
    for i in range(L):
        e = ('comp', ('lift', 'x', ('atom', i % 2)), e)
    return e


def wb(k):  # r_k := share r := r_{k-1} in ⟦x := u[r] | r⟧  (well behaved)
    e = ('atom', 0)
    for i in range(k):
        r = 'r%d' % i
        e = ('share', r, e, ('inner', 'x', U(0, ('pcomp', ('ref', r), ('pid',))), ('ref', r)))
    return e


def wb_lift(k):  # payload u[r] and tail under a slot ⟦· | r⟧ : leading shifts
    e = ('atom', 0)
    for i in range(k):
        r = 'r%d' % i
        e = ('share', r, e, ('inner', 'x', U(0, ('pcomp', ('ref', r), ('pid',))), ('lift', '.', ('ref', r))))
    return e


def bad(k):  # u[r][c1], v[r][c2] : not well behaved
    c1 = ('atom', 0); c2 = ('atom', 1)
    e = ('atom', 0)
    for i in range(k):
        r = 'r%d' % i
        e = ('share', r, e, ('inner', 'x', U(0, ('pcomp', c1, ('pcomp', ('ref', r), ('pid',)))),
                             ('inner', 'y', U(1, ('pcomp', c2, ('pcomp', ('ref', r), ('pid',)))), ('id',))))
    return e


def deep(L):  # x_i := u for i = 0..L-1, each via i lifts
    e = ('id',)
    for i in range(L):
        s = ('inner', 'x', U(i % 2), ('id',))
        for _ in range(i):
            s = ('lift', 'x', s)
        e = ('comp', s, e)
    return e


def run(name, f, ns):
    out = []
    for n in ns:
        G.reset()
        G.EVALS[0] = 0
        r = G.graph(f(n))
        out.append((n, G.size(r), G.EVALS[0]))
    print(name.ljust(10), ' '.join('n=%d:size=%d,evals=%d' % t for t in out))


#run('chain', chain, [10, 20, 40, 80])
#run('lifts', lifts, [10, 20, 40, 80])
#run('wb', wb, [10, 20, 40, 80])
#run('wb_lift', wb_lift, [10, 20, 40, 80])
#run('wb_lift∘c', lambda k: ('comp', ('inner', '.', U(1), ('id',)), wb_lift(k)), [10, 20, 40, 80])
#run('bad', bad, [4, 6, 8, 10])
#run('deep', deep, [10, 20, 40])
c_hard = ('inner', '.', U(1), ('atom', 1))
#run('wb_lift∘hard', lambda k: ('comp', c_hard, wb_lift(k)), [10, 20, 40, 80])
c_hard2 = ('lift', '.', ('inner', '.', U(1), ('atom', 1)))
#run('wb_lift∘hard2', lambda k: ('comp', c_hard2, wb_lift(k)), [10, 20, 40, 80])
