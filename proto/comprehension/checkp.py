import sys, random
from gmodel import env
from gmodel2 import GModel, check_commute
from check3 import load, run, fmt
from pnorm import N
def main(name,labels,LT,nmodels=40,seed=0):
    ws,ids=load(name); rng=random.Random(seed)
    models=[GModel(labels,LT,rng) for _ in range(nmodels)]
    for m in models: check_commute(m,rng)
    xs=[[env(m.tapes,rng=rng) for _ in range(2)] for m in models]
    def sig(w): return tuple(tuple(sorted(run(m,w,x).items())) for m,xx in zip(models,xs) for x in xx)
    sigs=[sig(w) for w in ws]
    nmean=len(set(sigs))
    for fix in (False,True):
        n=N(LT,fix); nf=[n.norm(w) for w in ws]
        cls={}
        for f,sg in zip(nf,sigs): cls.setdefault(f,set()).add(sg)
        unsound=sum(1 for v in cls.values() if len(v)>1)
        # agreement with HNorm ids
        agree = len(set(zip(nf,ids)))==len(set(nf))==len(set(ids)) if not fix else None
        print(f"{name} fix={fix}: classes={len(cls)} meaning classes={nmean} unsound={unsound} missed={len(cls)-nmean+unsound}"
              + (f" same partition as HNorm={agree}" if not fix else ""))
main(sys.argv[1], sys.argv[2].split(','), {tuple(p.split('<')) for p in sys.argv[3].split(',') if p})
