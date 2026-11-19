"""Timings of rforms.py on families of words, with the moves and swaps counted."""
import sys, time, random; sys.path.insert(0,'.')
from rforms import R
from forms import P
from pnorm import N
def mkN(n):
    o=N.__new__(N); o.fix=False
    o.LT={(f'l{i}',f'l{j}') for i in range(n) for j in range(i+1,n)}
    return o
def unN():
    o=N.__new__(N); o.fix=False; o.LT=set(); return o
def fam_chain(n):   # copies along an ordered chain, with weakenings: one growing form
    w=[]
    for i in range(n-1): w+= [('E',f'l{i}',(f'l{i+1}',0)), ('W',f'l{(i*7)%n}')]
    return ('C',w), mkN(n)
def fam_lifts(n):   # nested lifts over a weakening, unordered labels
    e=('W','k')
    for i in range(n): e=('Lift',f'a{i}',e)
    return e, unN()
def fam_lifts_ord(n):   # nested lifts, ordered labels (all absorbed)
    e=('W','l0')
    for i in range(1,n): e=('Lift',f'l{i}',e)
    return e, mkN(n)
def fam_blocked(n):  # many small blocked forms, weakening early that moves right through them
    w=[('W','k')]
    for i in range(n): w.append(('E',f'a{i}',('a0',0)))
    return ('C',w), unN()
def fam_random(n):
    rng=random.Random(n); labs=[f'l{i}' for i in range(8)]
    o=N.__new__(N); o.fix=False; o.LT={(f'l{i}',f'l{j}') for i in range(8) for j in range(i+1,8) if (i+j)%3}
    w=[]
    for _ in range(n):
        r=rng.random(); a=rng.choice(labs)
        if r<0.35: w.append(('W',a))
        elif r<0.8: w.append(('E',a,(rng.choice(labs),rng.randint(0,1))))
        else: w.append(('Lift',a,('W',rng.choice([x for x in labs if x!=a]))))
    return ('C',w), o
for name,fam in [('chain',fam_chain),('nested lifts',fam_lifts),('nested lifts, ordered',fam_lifts_ord),('blocked',fam_blocked),('random',fam_random)]:
    prev=None
    for n in [100,200,400,800]:
        e,nn=fam(n); r=R(nn)
        t=time.time(); fs=r.run(e); dt=time.time()-t
        ratio='' if prev is None else f'x{dt/prev:.1f}'
        print(f"{name:22} n={n:4} forms={len(fs):4} {dt:7.3f}s {ratio:6} moves={r.stats['moves']} swaps={r.stats['swaps']}",flush=True); prev=max(dt,1e-4)


fams={
 'weakenings, unordered': lambda n: ('C',[('W',f'a{i}') for i in range(n)]),
 'copies, unordered':     lambda n: ('C',[('E',f'a{i}',(f'a{i}',0)) for i in range(n)]),
 'weak then copy each':   lambda n: ('C',[x for i in range(n) for x in (('W',f'a{i}'),('E',f'b{i}',(f'a{i}',0)))]),
}
for name,fam in fams.items():
    prev=None
    for n in [500,1000,2000,4000]:
        r=R(unN()); e=fam(n)
        t=time.time(); fs=r.run(e); dt=time.time()-t
        print(f"{name:22} n={n:5} forms={len(fs):5} {dt:7.3f}s {'' if prev is None else 'x%.1f'%(dt/prev)} moves={r.stats['moves']}",flush=True); prev=max(dt,1e-4)
