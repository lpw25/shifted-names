import json, re, random, sys
from gmodel import env
from gmodel2 import GModel, check_commute
def load(name):
    out=open(f'coq/{name}.out').read()
    ids=[int(x) for x in re.findall(r'(\d+)%positive', out)]
    ws=[[tuple(tuple(x) if isinstance(x,list) else x for x in s) for s in w] for w in json.load(open(f'coq/{name}.json'))]
    assert len(ids)==len(ws), (len(ids),len(ws))
    return ws,ids
def name_val(m,x,k,i):
    for _ in range(i): x,_=m.pop(k,x)
    return m.pop(k,x)[1]
def run(m,w,x):
    for s in reversed(w):
        if s[0]=='W': x,_=m.pop(s[1],x)
        elif s[0]=='L':
            y,t=m.pop(s[1],x); y,_=m.pop(s[2],y); x=m.push(s[1],y,t)
        else:
            t=s[2]
            v=m.consts.setdefault(t,random.randrange(10**6)) if t[0]=='b' else name_val(m,x,t[1],t[2])
            x=m.push(s[1],x,v)
    return x
def fmt(w):
    def f(s):
        if s[0]=='W': return 'W'+s[1]
        if s[0]=='L': return f'L{s[1]}(W{s[2]})'
        t=s[2]; return 'E'+s[1]+('(·%d)'%t[1] if t[0]=='b' else '(%s%d)'%(t[1],t[2]))
    return ' '.join(map(f,w)) or 'id'
def main(name,labels,LT,nmodels=40,seed=0):
    ws,ids=load(name); rng=random.Random(seed)
    models=[GModel(labels,LT,rng) for _ in range(nmodels)]
    for m in models: check_commute(m,rng)
    xs=[[env(m.tapes,rng=rng) for _ in range(2)] for m in models]
    def sig(w): return tuple(tuple(sorted(run(m,w,x).items())) for m,xx in zip(models,xs) for x in xx)
    groups={}
    for w,i in zip(ws,ids): groups.setdefault(i,[]).append(w)
    unsound=[]; sigs={}
    for i,g in groups.items():
        s=[sig(w) for w in g]
        if len(set(s))>1: unsound.append(g)
        sigs.setdefault(s[0],[]).append(i)
    merged=[v for v in sigs.values() if len(v)>1]
    print(f"{name}: words={len(ws)} HNorm classes={len(groups)} unsound classes={len(unsound)} "
          f"meaning classes={len(sigs)} HNorm classes merged by all sampled models={sum(len(v)-1 for v in merged)}")
    for g in unsound[:6]: print('  unsound:', ' | '.join(fmt(w) for w in g[:4]))
    for v in merged[:8]: print('  merged:', ' | '.join(fmt(groups[i][0]) for i in v[:4]))
if __name__=='__main__':
    which=sys.argv[1]
    if which=='abv4': main('abv4',['a','b'],set())
    if which=='ghmv3': main('ghmv3',['g','h','m'],{('g','h')})
