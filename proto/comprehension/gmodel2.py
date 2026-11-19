"""Generic comprehension models in Set.  c_l = (structural pop of tape tau(l)) o M_l, where M_l is
an invertible map on the first K cells of the tapes in a region R_l (containing tau(l)).
Labels the facts order get disjoint regions, so their comprehensions commute."""
import random
from gmodel import P, ordered, env
K=3
class GModel:
    def __init__(s,labels,LT,rng,share=0.3,regsize=2,nops=12):
        LT=set(LT); ch=True
        while ch:                                   # the facts are transitive
            ch=False
            for (a,b) in list(LT):
                for (c,d) in list(LT):
                    if b==c and (a,d) not in LT: LT.add((a,d)); ch=True
        s.labels=labels; s.LT=LT; s.consts={}
        s.tau={l:l for l in labels}
        for l in labels:
            if rng.random()<share:
                c=[k for k in labels if k!=l and not ordered(LT,l,k) and all(not ordered(LT,l,j) for j in labels if s.tau[j]==s.tau[k])]
                if c: s.tau[l]=s.tau[rng.choice(c)]
        s.tapes=sorted(set(s.tau.values()))
        # region: own tape plus tapes not touched by labels ordered against l
        s.reg={}
        for l in labels:
            ok=[T for T in s.tapes if T!=s.tau[l] and not any(ordered(LT,l,j) and (T==s.tau[j]) for j in labels)]
            s.reg[l]=[s.tau[l]]+rng.sample(ok,min(len(ok),rng.randint(0,regsize)))
        # make regions of ordered pairs disjoint: drop shared tapes from the later label
        for a in labels:
            for b in labels:
                if a<b and ordered(LT,a,b):
                    s.reg[b]=[T for T in s.reg[b] if T==s.tau[b] or T not in s.reg[a]]
                    s.reg[a]=[T for T in s.reg[a] if T==s.tau[a] or T not in s.reg[b]]
        s.ops={}
        for l in labels:
            cells=[(T,i) for T in s.reg[l] for i in range(K)]
            s.ops[l]=[(rng.choice(cells),rng.choice(cells),rng.randrange(1,P)) for _ in range(nops)]
            s.ops[l]=[(a,b,c) for a,b,c in s.ops[l] if a!=b]
    def mix(s,l,x,inv=False):
        x={T:list(v) for T,v in x.items()}
        ops=reversed(s.ops[l]) if inv else s.ops[l]
        for (Ta,ia),(Tb,ib),c in ops:
            x[Tb][ib]=(x[Tb][ib]+(-c if inv else c)*x[Ta][ia])%P
        return {T:tuple(v) for T,v in x.items()}
    def pop(s,l,x):
        x=s.mix(l,x); T=s.tau[l]; q=x[T][0]; x=dict(x); x[T]=x[T][1:]; return x,q
    def push(s,l,x,t):
        T=s.tau[l]; x=dict(x); x[T]=(t%P,)+x[T]; return s.mix(l,x,inv=True)
    def run(s,w,x):
        for st in reversed(w):
            if st[0]=='W': x,_=s.pop(st[1],x)
            else: x=s.push(st[1],x,s.consts.setdefault(st[2],random.randrange(P)))
        return x
def check_commute(m,rng):
    """ordered pairs: pops/pushes commute"""
    for a in m.labels:
        for b in m.labels:
            if a!=b and ordered(m.LT,a,b):
                x=env(m.tapes,rng=rng)
                y1,qa1=m.pop(a,x); y1,qb1=m.pop(b,y1)
                y2,qb2=m.pop(b,x); y2,qa2=m.pop(a,y2)
                assert y1==y2 and qa1==qa2 and qb1==qb2, (a,b)
