"""Canonicity check of rforms.py: the pass, then HNorm without relnf, against HNorm with relnf."""
import sys; sys.path.insert(0,'.')
from rforms import R, of_word
from forms import norm_forms
from pnorm import N, BOUND
from check3 import fmt
import checkpy
def main(labels,LT,n,vidx=(0,1),lifts=True,show=2):
    nf=N(LT,True); nn=N(LT,False); r=R(nn)
    A={}; bad=0
    for w in checkpy.words(labels,n,vidx,lifts):
        fs=r.run(of_word(w,BOUND)); b=nf.norm(tuple(w))
        if any(k[0]=='A' for k in fs): raise Exception
        if norm_forms(nf,fs)!=b: bad+=1
        A.setdefault(b,{}).setdefault(norm_forms(nn,fs),(w,fs))
    split=sorted([v for v in A.values() if len(v)>1],key=lambda v: sum(len(w) for (w,_) in v.values()))
    print(labels,sorted(LT),n,'unsound:',bad,'split:',len(split),'classes',len(A),flush=True)
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
