import itertools, json
def gen(labels, n, facts, name, ntg=1, vidx=(0,1), lifts=True, skipcancel=True):
    steps=[('W',l) for l in labels]+[('E',l,('b',k)) for l in labels for k in range(ntg)]
    steps+=[('E',l,('v',k,i)) for l in labels for k in labels for i in vidx]
    if lifts: steps+=[('L',l,k) for l in labels for k in labels if k!=l]
    words=[]
    for k in range(n+1):
        for w in itertools.product(steps, repeat=k):
            if skipcancel and any(s[0]=='W' and t[0]=='E' and s[1]==t[1] for s,t in zip(w,w[1:])): continue
            words.append(w)
    lid={l:i for i,l in enumerate(labels)}
    def st(s):
        if s[0]=='W': return f"(W (LAtom {lid[s[1]]}))"
        if s[0]=='L': return f"(ALift (LAtom {lid[s[1]]}) (W (LAtom {lid[s[2]]})))"
        t=s[2]
        tg=f"(TVarE LNone {t[1]})" if t[0]=='b' else f"(TVarE (LAtom {lid[t[1]]}) {t[2]})"
        return f"(AInner (LAtom {lid[s[1]]}) {tg} AId)"
    hdr=["From Stdlib Require Import List PArith.","Import ListNotations.","From ShiftedNames.Core Require Import Normalise HNorm.",
      "Definition W (h : lexp) : aexp := AOuter h AId.",
      "Definition gseq (p q : aexp) : aexp := ACompose q p.",
      "Fixpoint gseqs (l : list aexp) : aexp := match l with [] => AId | [p] => p | p :: r => gseq p (gseqs r) end.",
      f"Definition F := order_of [{'; '.join(f'(LAtom {lid[a]}, LAtom {lid[b]})' for a,b in facts)}].",
      "Fixpoint ids (l : list aexp) (S : st) : list positive * st := match l with [] => ([], S) | e :: r => let '(w, S1) := norm F e [] S in let '(l', S2) := ids r S1 in (wid w :: l', S2) end."]
    out=list(hdr); C=1500
    prev="st0"
    for ci in range(0,len(words),C):
        ch=words[ci:ci+C]; j=ci//C
        out.append(f"Definition ws{j} : list aexp := [")
        out.append(";\n".join("gseqs ["+"; ".join(st(s) for s in w)+"]" for w in ch)+"].")
        out.append(f"Definition r{j} := Eval vm_compute in ids ws{j} {prev}.")
        out.append(f"Eval vm_compute in fst r{j}.")
        prev=f"(snd r{j})"
    open(f'coq/{name}.v','w').write("\n".join(out)+"\n")
    json.dump([[list(s) for s in w] for w in words], open(f'coq/{name}.json','w'))
    print(name,len(words))
if __name__=='__main__':
    import sys
    gen(['a','b'],4,[],'abv4')
    gen(['g','h','m'],3,[('g','h')],'ghmv3')
