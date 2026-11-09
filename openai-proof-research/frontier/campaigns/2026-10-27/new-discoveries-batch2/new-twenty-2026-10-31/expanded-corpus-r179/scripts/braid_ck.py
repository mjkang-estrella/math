# Test the stronger per-Coxeter-Knuth-class version of Elder's Conj. path1: in each CK class K of reduced words,
# sum_{w in K} #{j: w_j = w_{j+2}} <= |K|.  CK relations (Edelman-Greene): i,i+1,i ~ i+1,i,i+1; x z y ~ z x y and
# y x z ~ y z x for x<y<z (applied to consecutive positions).
import sys, itertools
n=int(sys.argv[1])
def words(p):
    # all reduced words of p (as tuples of generator indices 1..n-1, left-to-right, p = s_{w1}...s_{wl} acting on positions)
    p=list(p); res=[]
    def rec(q,suffix):
        D=[k for k in range(n-1) if q[k]>q[k+1]]
        if not D: res.append(tuple(suffix)); return
        for k in D:
            q[k],q[k+1]=q[k+1],q[k]; rec(q,[k+1]+suffix); q[k],q[k+1]=q[k+1],q[k]
    rec(p,[]); return res
def ck_neighbors(w):
    out=[]
    for j in range(len(w)-2):
        a,b,c=w[j],w[j+1],w[j+2]
        if a==c and abs(a-b)==1: out.append(w[:j]+(b,a,b)+w[j+3:])
        else:
            # x z y ~ z x y  (x<y<z): first two swap when third lies strictly between
            if min(a,b)<c<max(a,b): out.append(w[:j]+(b,a,c)+w[j+3:])
            # y x z ~ y z x : last two swap when first lies strictly between
            if min(b,c)<a<max(b,c): out.append(w[:j]+(a,c,b)+w[j+3:])
    return out
worst=0; classes=0; viol=0; maxratio=0
for p in itertools.permutations(range(n)):
    W=words(p)
    if len(W)>300000: continue
    Wset=set(W); seen=set()
    for w in W:
        if w in seen: continue
        comp=[w]; seen.add(w); i=0
        while i<len(comp):
            for u in ck_neighbors(comp[i]):
                if u not in seen: seen.add(u); comp.append(u)
            i+=1
        assert all(u in Wset for u in comp)
        br=sum(1 for u in comp for j in range(len(u)-2) if u[j]==u[j+2])
        classes+=1; r=br/len(comp); maxratio=max(maxratio,r)
        if br>len(comp): viol+=1; print("VIOLATION",p,len(comp),br)
        if len(sys.argv)>2 and br*1.0>=float(sys.argv[2])*len(comp) and br>0: print("NEAR",p,"size",len(comp),"braids",br,"rep",comp[0])
print('n',n,'CK classes',classes,'violations',viol,'max braid/size',maxratio)
