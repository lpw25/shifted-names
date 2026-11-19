"""A pure (unshared) copy of HNorm, with an optional fix: a stuck lookup of g keeps only the steps of
its word that can affect it (relnf)."""
BOUND='·'
class N:
    def __init__(s, LT, fix=True):
        s.LT=set(LT); s.fix=fix
        ch=True
        while ch:                                   # transitive closure
            ch=False
            for (a,b) in list(s.LT):
                for (c,d) in list(s.LT):
                    if b==c and (a,d) not in s.LT: s.LT.add((a,d)); ch=True
    def before(s,a,b): return a!=b and ((a,b) in s.LT or (b==BOUND and a!=BOUND))
    def kd(s,a,b): return s.before(a,b) or s.before(b,a)
    def relnf(s,g,w):
        if not s.fix: return w
        out=[]; kept=set(); atom=False
        for st in w:
            if st[0]!='A' and out and not atom and s.kd(g,st[1]) and all(s.kd(st[1],m) for m in kept): continue
            out.append(st)
            if st[0]=='A': atom=True
            else: kept.add(st[1])
        return tuple(out)
    def lookup(s,h,i,w):
        for j,st in enumerate(w):
            if st[0]=='A': return ('L',h,i,s.relnf(h,w[j:]))
            g=st[1]
            if g==h:
                if st[0]=='E':
                    if i==0: return st[2]
                    i-=1
                else: i+=1
            elif not s.kd(g,h): return ('L',h,i,s.relnf(h,w[j:]))
        return ('V',h,i)
    def stop(s,h,w):
        j=0
        while j<len(w) and w[j][0]!='A' and s.before(w[j][1],h): j+=1
        return w[:j],w[j:]
    def pushW(s,h,w):
        p,r=s.stop(h,w)
        if r and r[0][0]=='E' and r[0][1]==h: return p+r[1:]
        return p+(('W',h),)+r
    def pushE(s,h,v,w):
        p,r=s.stop(h,w)
        if r and r[0][0]=='W' and r[0][1]==h and v==s.lookup(h,0,r[1:]): return p+r[1:]
        return p+(('E',h,v),)+r
    def tval(s,t,K):
        if t[0]=='b': return s.lookup(BOUND,t[1],K)
        return s.lookup(t[1],t[2],K)
    def norm(s,word):
        K=()
        for st in reversed(word):
            if st[0]=='W': K=s.pushW(st[1],K)
            elif st[0]=='E': K=s.pushE(st[1],s.tval(st[2],K),K)
            elif st[0]=='L':
                l,k=st[1],st[2]
                v=s.lookup(l,0,K); K1=s.pushW(l,K); K2=s.pushW(k,K1); K=s.pushE(l,v,K2)
        return K
