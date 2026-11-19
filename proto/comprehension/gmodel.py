"""Comprehension models in Set.  Each label l pops/pushes a tape tau(l); its head is
q_l(x) = x[tau l][0] + sum_k lam[l][k] * x[k][0]  (k tapes other than tau l).
A word s1..sn means s1 o ... o sn on environments: sn is applied first.
W h = p_h (pop),  E h t = <id, t>_h (push the value of t)."""
import random
P=1000003
def ordered(LT,a,b): return (a,b) in LT or (b,a) in LT

class Model:
    def __init__(s, labels, LT, tau, lam, consts):
        s.labels,s.LT,s.tau,s.lam,s.consts=labels,LT,tau,lam,consts
    def reads(s,l): return {k for k,c in s.lam[l].items() if c}
    def check(s):
        for a in s.labels:
            for b in s.labels:
                if a!=b and ordered(s.LT,a,b):
                    assert s.tau[a]!=s.tau[b] and s.tau[b] not in s.reads(a) and s.tau[a] not in s.reads(b), (a,b)
    def corr(s,l,x): return sum(c*x[k][0] for k,c in s.lam[l].items())%P
    def push(s,l,x,t):
        T=s.tau[l]; x=dict(x); x[T]=((t-s.corr(l,x))%P,)+x[T]; return x
    def pop(s,l,x):
        T=s.tau[l]; q=(x[T][0]+s.corr(l,x))%P; x=dict(x); x[T]=x[T][1:]; return x,q
    def run(s,w,x):
        for st in reversed(w):
            if st[0]=='W': x,_=s.pop(st[1],x)
            else: x=s.push(st[1],x,s.consts.setdefault(st[2],random.randrange(P)))
        return x

def env(tapes,L=40,rng=random):
    return {T:tuple(rng.randrange(P) for _ in range(L)) for T in tapes}

def random_model(labels,LT,rng,share=0.5,mix=0.5):
    tau={l:l for l in labels}
    for l in labels:                       # maybe share a tape with an unordered label
        if rng.random()<share:
            cands=[k for k in labels if k!=l and not ordered(LT,l,k)
                   and all(not ordered(LT,l,j) for j in labels if tau[j]==tau[k])]
            if cands: tau[l]=tau[rng.choice(cands)]
    tapes=sorted(set(tau.values()))
    lam={}
    for l in labels:
        lam[l]={}
        for T in tapes:
            if T==tau[l]: continue
            if any(ordered(LT,l,j) for j in labels if tau[j]==T): continue
            if rng.random()<mix: lam[l][T]=rng.randrange(1,P)
    m=Model(labels,LT,tau,lam,{}); m.check(); return m,tapes

def same(m,tapes,w1,w2,rng,trials=3):
    for _ in range(trials):
        x=env(tapes,rng=rng)
        if m.run(w1,x)!=m.run(w2,x): return False
    return True
