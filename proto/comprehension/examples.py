import random
from gmodel import env
from gmodel2 import GModel, check_commute
from check3 import run
W=lambda h:('W',h)
def E(h,t): return ('E',h,('b',t) if isinstance(t,(int,str)) else t)
def test(name,labels,LT,w1,w2,n=300,seed=0):
    rng=random.Random(seed); sep=0
    for _ in range(n):
        m=GModel(labels,LT,rng); check_commute(m,rng)
        x=env(m.tapes,rng=rng)
        if run(m,w1,x)!=run(m,w2,x): sep+=1
    print(f"{name}: separated in {sep}/{n} generic comprehension models")
# facts example (g<h, m unrelated)
P=[W('h'),E('m',2),W('m'),E('h',0)]
test('facts example',['g','h','m'],{('g','h')},P+[E('g',0),W('g'),E('m',1),W('m')],P+[E('m',1),W('m'),E('g',0),W('g')])
# joint example (a<g, b<m)
Q=[W('b'),W('a'),E('m',2),W('m'),E('a',9),E('b',9)]
test('joint example',['a','b','g','m'],{('a','g'),('b','m')},Q+[E('g',0),W('g'),E('m',1),W('m')],Q+[E('m',1),W('m'),E('g',0),W('g')])
# example 1
test('example 1',['x','y'],set(),[W('x'),W('y'),E('x','u'),E('y','v')],[W('y'),W('x'),E('y','v'),E('x','u')])
# example 2 (x<m, k unrelated): W(u) vs W(u')
test('example 2',['x','m','k'],{('x','m')},[W('x'),W('k'),E('m','c'),E('k','v'),E('x','u')],[W('x'),W('k'),E('m','c'),E('k','v'),E('x','u2')])
# HEtaGap t1/t2 and r1/r2, HNormGap f1/f2 (labels a, b unordered)
En=lambda h,n:E(h,n)
t1=[En('a',0),W('a'),En('b',0),W('b')]; t2=[En('b',0),W('b'),En('a',0),W('a')]
test('t1/t2',['a','b'],set(),t1,t2)
r1=[W('b'),W('b'),En('a',2),W('a'),En('b',0),En('b',0),En('a',0),W('a'),W('b'),En('a',1),W('a')]
r2=[W('b'),W('b'),En('a',2),W('a'),En('b',0),En('a',1),W('a'),En('b',0),En('a',0),W('a'),W('b')]
test('r1/r2',['a','b'],set(),r1,r2)
f1=[W('a'),En('b',0),W('b')]; f2=f1+[En('a',1),W('a')]
test('f1/f2',['a','b'],set(),f1,f2)
# sanity: identities that must hold
test('cancellation  W a; E a = id',['a','b'],set(),[W('a'),E('a',3)],[])
test('lift law  L g(W h) = W h',['g','h','m'],{('g','h')},[('L','g','h')],[W('h')])
test('ordered commute  W g W h = W h W g',['g','h','m'],{('g','h')},[W('g'),W('h')],[W('h'),W('g')])
test('unordered  W a W b vs W b W a',['a','b'],set(),[W('a'),W('b')],[W('b'),W('a')])
