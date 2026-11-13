import graph as G
from printer3 import to_expr


def pa(e):
    t = e[0]
    if t == 'id': return 'id'
    if t == 'atom': return 'σ%d' % e[1]
    if t == 'comp': return '(%s ∘ %s)' % (pa(e[1]), pa(e[2]))
    if t == 'outer': return '↑%s(%s)' % (e[1], pa(e[2]))
    if t == 'lift': return '⟦%s· | %s⟧' % (e[1], pa(e[2]))
    if t == 'inner': return '⟦%s := %s | %s⟧' % (e[1], pt(e[2]), pa(e[3]))
    if t == 'share': return 'share %s := %s in\n  %s' % (e[1], pa(e[2]), pa(e[3]))
    if t == 'ref': return e[1]
    if t == 'labels':
        parts = [(l, L) for l, L in e[1] if L != ('lof', l, ('id',))]
        return '⟦' + '; '.join('%s: %s' % (l, pl(L)) for l, L in parts) + '⟧'
    return str(e)


def pl(L):
    if L[0] == 'lcons': return '%s, %s' % (pt(L[1]), pl(L[2]))
    return '…%s' % pa(L[2])


def pt(t):
    if t[0] == 'tvar': return '%s%d' % (t[1], t[2])
    if t[0] == 'tbind': return 'u%d[%s]' % (t[1], pp(t[2]))
    if t[0] == 'tvia': return '%s%d via %s' % (t[1][0], t[1][1], pa(t[2]))
    if t[0] == 'tshift': return '↑' + pt(t[2])
    return str(t)


def pp(p):
    if p[0] == 'pid': return 'id'
    if p[0] == 'patom': return 'ρ%d' % p[1]
    if p[0] == 'pcomp': return '%s ∘ %s' % (pa(p[1]), pp(p[2]))
    return str(p)


def show(name, e):
    G.reset()
    print('==', name, '\n  in :', pa(e), '\n  out:', pa(to_expr(G.graph(e))))


U = lambda u=0: ('tbind', u, ('pid',))
show('hop', ('comp', ('inner', 'x', U(), ('id',)), ('atom', 0)))
show('hop2', ('comp', ('lift', 'x', ('atom', 0)), ('inner', 'x', ('tbind', 0, ('pcomp', ('atom', 0), ('pid',))), ('id',))))
show('chain3', ('comp', ('inner', 'x', U(0), ('id',)), ('comp', ('inner', 'x', U(1), ('id',)), ('inner', 'x', U(0), ('id',)))))
show('subst-then-atom', ('comp', ('atom', 1), ('inner', 'y', U(0), ('lift', 'x', ('id',)))))
