"""Exhaustive check of the fixed pure normaliser against generic comprehension models (no Coq)."""
import sys, random, itertools
from gmodel import env
from gmodel2 import GModel, check_commute
from check3 import run, fmt
from pnorm import N
def words(labels,n,vidx=(0,1),lifts=True):
    steps=[('W',l) for l in labels]+[('E',l,('b',0)) for l in labels]
    steps+=[('E',l,('v',k,i)) for l in labels for k in labels for i in vidx]
    if lifts: steps+=[('L',l,k) for l in labels for k in labels if k!=l]
    for k in range(n+1):
        for w in itertools.product(steps, repeat=k):
            if any(s[0]=='W' and t[0]=='E' and s[1]==t[1] for s,t in zip(w,w[1:])): continue
            yield list(w)
def main(labels,LT,n,nmodels=30,seed=0,vidx=(0,1),lifts=True):
    rng=random.Random(seed)
    models=[GModel(labels,LT,rng) for _ in range(nmodels)]
    for m in models: check_commute(m,rng)
    xs=[env(m.tapes,rng=rng) for m in models]
    nn=N(LT,True); cls={}; sigs=set(); ex=[]
    for w in words(labels,n,vidx,lifts):
        sg=tuple(tuple(sorted(run(m,w,x).items())) for m,x in zip(models,xs))
        sigs.add(sg)
        f=nn.norm(tuple(w)); cls.setdefault(f,{}).setdefault(sg,w)
    unsound=[v for v in cls.values() if len(v)>1]
    byf={}
    for f,v in cls.items():
        for sg in v: byf.setdefault(sg,[]).append(f)
    missed=[v for v in byf.values() if len(v)>1]
    print(f"{labels} {sorted(LT)} n<={n}: classes={len(cls)} meanings={len(sigs)} unsound={len(unsound)} missed={sum(len(v)-1 for v in missed)}")
    for v in unsound[:3]: print('  unsound:',' | '.join(fmt(w) for w in v.values()))
if __name__=='__main__':
    main(['g','h','k'],{('g','h'),('k','h')},3)
    main(['a','b','c'],{('a','b'),('b','c')},3)
    main(['a','b','c','d'],{('a','c'),('b','c'),('c','d')},2)
    main(['a','b','c','d'],{('a','b'),('c','d')},3,vidx=(0,),lifts=False)
