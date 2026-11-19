"""Context forms and the left-to-right pass of Core/CForm.v, in Python; then HNorm without relnf
(pnorm.N(fix=False)) is compared with HNorm with relnf on every word."""
import sys; sys.path.insert(0,'.')
import random
from check3 import fmt
from pnorm import N, BOUND
import checkpy
def lab(v): return BOUND if v[0]=='b' else v[1]
def idx(v): return v[1] if v[0]=='b' else v[2]
# Form (O, I): outputs O (popped in order, O[0] first); inputs I outermost first, (label, (z, i, d)):
# the target is the name z_i read after popping O[0..d-1].
def of_step(st):
    if st[0]=='W': return ((st[1],),())
    if st[0]=='E': return ((), ((st[1],(lab(st[2]),idx(st[2]),0)),))
    if st[0]=='L': return ((st[1],st[2]),((st[1],(st[1],0,0)),))
class P:
    def __init__(s,n): s.n=n
    def kd(s,a,b): return s.n.kd(a,b)
    def nread(s,O,r):
        z,i,d=r
        while d>0:
            o=O[d-1]
            if o==z: i+=1; d-=1
            elif s.kd(z,o): d-=1
            else: break
        return (z,i,d)
    def compose(s,F1,F2):          # F1 first on variables; None if blocked
        O1,I1=F1; O2,I2=F2
        rem=list(I2); passed=[]; states=[(list(rem),0)]
        for o in O1:
            for p,(l,t) in enumerate(rem):
                if l==o: del rem[p]; break
                if not s.kd(l,o): return None
            else: passed.append(o)
            states.append((list(rem),len(passed)))
        O=tuple(O2)+tuple(passed)
        def read(r):
            z,i,d=r; rm,pc=states[d]
            for (l,t) in rm:
                if l==z:
                    if i==0: return t
                    i-=1
                elif not s.kd(l,z): return None
            return s.nread(O,(z,i,len(O2)+pc))
        newI=[]
        for (l,t) in I1:
            r=read(t)
            if r is None: return None
            newI.append((l,r))
        return s.tidy((O,tuple(newI)+tuple(rem)))
    def tidy(s,F):
        O,I=list(F[0]),[(l,s.nread(F[0],t)) for (l,t) in F[1]]
        ch=True
        while ch:
            ch=False
            for k in range(len(I)-1):
                (a,_),(b,_)=I[k],I[k+1]
                if s.kd(a,b) and s.n.before(b,a): I[k],I[k+1]=I[k+1],I[k]; ch=True
            for k in range(len(O)-1):
                a,b=O[k],O[k+1]
                if not (s.kd(a,b) and s.n.before(b,a)): continue
                newI=[]
                for (l,(z,i,d)) in I:
                    if d==k+1:          # read after a, before b: after the swap read after both
                        if z==b:
                            if i==0: newI=None; break
                            newI.append((l,(z,i-1,k+2)))
                        elif s.kd(z,b): newI.append((l,(z,i,k+2)))
                        else: newI=None; break
                    else: newI.append((l,(z,i,d)))
                if newI is None: continue
                O[k],O[k+1]=b,a; I=[(l,s.nread(O,t)) for (l,t) in newI]; ch=True
            if not ch:
                r=s.absorb(O,I)
                if r: O,I=r; ch=True
        return (tuple(O),tuple(I))
    def absorb(s,O,I):
        n=len(O)
        for p,(l,t) in enumerate(I):
            for j in range(n):
                if O[j]!=l or t!=(l,0,j): continue
                if not all(s.kd(l,o) for o in O[j+1:]): continue
                if not all(s.kd(l,m) for (m,_) in I[p+1:]): continue
                newI=[]
                for q,(m,(z,i,d)) in enumerate(I):
                    if q==p: continue
                    if d<=j: newI.append((m,(z,i,d))); continue
                    if z==l: newI.append((m,(z,i+1,d-1)))
                    elif s.kd(z,l): newI.append((m,(z,i,d-1)))
                    else: newI=None; break
                if newI is None: continue
                O2=O[:j]+O[j+1:]
                return O2,[(m,s.nread(O2,r)) for (m,r) in newI]
        return None
    def transfer(s,F1,F2):        # a top-movable output of F1 moves into F2
        O1,I1=F1
        for j,o in enumerate(O1):
            if not all(s.kd(o,a) for a in O1[:j]): continue
            newI=[]
            for (m,(z,i,d)) in I1:
                if d>j: newI.append((m,(z,i,d-1))); continue
                if z==o:
                    if i==0: newI=None; break
                    newI.append((m,(z,i-1,d)))
                elif s.kd(z,o): newI.append((m,(z,i,d)))
                else: newI=None; break
            if newI is None: continue
            G=s.compose(((o,),()),F2)
            if G is None: continue
            O1n=O1[:j]+O1[j+1:]
            return s.tidy((O1n,tuple(newI))), G
        for p,(h,(z,i,d)) in enumerate(I1):
            if not all(s.kd(h,m) for (m,_) in I1[p+1:]): continue
            if not all(s.kd(h,o) for o in O1): continue
            ok=True
            for o in O1[:d]:
                if o==z: i+=1
                elif not s.kd(z,o): ok=False
            if not ok: continue
            newI=[]
            for q,(m,(y,k,e)) in enumerate(I1):
                if q==p: continue
                if y==h: newI.append((m,(y,k+1,e)))
                elif s.kd(y,h): newI.append((m,(y,k,e)))
                else: newI=None; break
            if newI is None: continue
            G=s.compose(((),((h,(z,i,0)),)),F2)
            if G is None: continue
            return s.tidy((O1,tuple(newI))), G
        return None
    def run(s,w):
        out=[]
        for st in w:
            F=s.tidy(of_step(st))
            while out:
                G=s.compose(out[-1],F)
                if G is not None: F=G; out.pop(); continue
                T=s.transfer(out[-1],F)
                if T is None: break
                out[-1],F=T
                if out[-1]==((),()): out.pop()
            out.append(F)
        return tuple(f for f in out if f!=((),()))
def norm_forms(n,fs):
    K=()
    for F in reversed(fs):
        O,I=F
        vals=[]
        for (l,(z,i,d)) in I:
            KK=K
            for o in O[:d]: KK=n.pushW(o,KK)
            vals.append(n.lookup(z,i,KK))
        Kt=K
        for o in O: Kt=n.pushW(o,Kt)
        for (l,_),v in reversed(list(zip(I,vals))): Kt=n.pushE(l,v,Kt)
        K=Kt
    return K
def main(labels,LT,n,vidx=(0,1),lifts=True,show=2):
    nf=N(LT,True); nn=N(LT,False); p=P(nn)
    A={}; bad=0; S={}
    for w in checkpy.words(labels,n,vidx,lifts):
        fs=p.run(w); b=nf.norm(tuple(w))
        if norm_forms(nf,fs)!=b: bad+=1
        A.setdefault(b,{}).setdefault(norm_forms(nn,fs),(w,fs))
        S.setdefault(fs,set()).add(b)
    split=sorted([v for v in A.values() if len(v)>1],key=lambda v: sum(len(w) for (w,_) in v.values()))
    print(labels,sorted(LT),n,'unsound:',bad,'split:',len(split),'distinct pass results',len(S),'classes',len(A),flush=True)
    for v in split[:show]:
        for (w,fs) in v.values(): print('   ',fmt(w),'->',fs)
        print()
if __name__=='__main__':
    main(['g','h','k'],{('g','h'),('k','h')},3)
    main(['g','h','k','m'],{('g','h'),('k','h'),('m','h')},3,lifts=False)
    main(['a','b','c'],{('a','b'),('b','c')},3)
    main(['a','b'],set(),4)
    main(['g','h','m'],{('g','h')},3)
    main(['a','b','c','d'],{('a','c'),('b','c'),('c','d')},2)

