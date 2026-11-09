# Check the combinatorial step of the proof of 362785: every closed-under-LemmaB residue walk of length L on Z_q
# (steps +-1; path edges at index distance >=3 have distinct classes {s,s+1}) has an 'independent transversal':
# one path index per residue, pairwise non-consecutive. Report counts for L=3q-2 (expect: all have one) and L=3q-3.
import sys
def cls(a,b,q): return frozenset((a%q,b%q))
def walks(q,L):
    r=[0]*L
    def rec(k,classes):
        if k==L: yield list(r); return
        for d in (1,-1):
            r[k]=(r[k-1]+d)%q
            c=cls(r[k-1],r[k],q); j=k  # edge index j (edge between k-1 and k)
            if any(cc==c and j-jj>=3 for jj,cc in classes): continue
            yield from rec(k+1,classes+[(j,c)])
    r[0]=0
    yield from rec(1,[])
def has_transversal(w,q):
    L=len(w); pos={s:[i for i in range(L) if w[i]==s] for s in range(q)}
    if any(not pos[s] for s in range(q)): return False
    chosen=[None]*q
    def rec(s):
        if s==q: return True
        for i in pos[s]:
            if all(chosen[t] is None or abs(chosen[t]-i)!=1 for t in range(s)):
                chosen[s]=i
                if rec(s+1): return True
        chosen[s]=None
        return False
    return rec(0)
for q in range(3,int(sys.argv[1])+1,2):
    for L in (3*q-3,3*q-2):
        tot=0; without=0; ex=None
        for w in walks(q,L):
            tot+=1
            if not has_transversal(w,q):
                without+=1; ex=ex or w
        print('q',q,'L',L,'LemmaB-walks',tot,'without independent transversal',without,'example',ex,flush=True)
