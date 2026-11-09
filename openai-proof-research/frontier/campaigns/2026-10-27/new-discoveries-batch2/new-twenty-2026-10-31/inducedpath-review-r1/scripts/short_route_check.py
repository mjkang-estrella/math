"""Reviewer's own code. Sanity check of the intermediate claim of the reviewer's SHORT route:
in the rotated linear model on [0,n-2] of G_{q,p}, every induced matching M of q-1 edges has
distinct residue classes K_j={c+j,c+j+1} (j=1..q-1, one class {c,c+1} missing) and, writing
A_j (residue c+j+1), B_j (residue c+j) for the endpoints of the class-K_j edge,
A_1<...<A_{q-1}<B_1<...<B_{q-1}.  Also re-checks no vertex is anticomplete to M."""
import sys,time
q=int(sys.argv[1]); p=int(sys.argv[2]); cap=float(sys.argv[3])
n=q*p-2; m=n-1
def adj(i,j):
    if i>j: i,j=j,i
    return j-i==1 or (j-i)%q==q-1
E=[(a,b) for a in range(m) for b in range(a+1,m) if adj(a,b)]
cnt=0; bad=0; extra=0; t0=time.time()
def check(M):
    global cnt,bad,extra
    cnt+=1
    cl=[frozenset((a%q,b%q)) for a,b in M]
    if len(set(cl))!=q-1: bad+=1; return
    allc={frozenset((s,(s+1)%q)) for s in range(q)}
    miss=list(allc-set(cl))[0]
    # c such that missing = {c,c+1}
    c=[s for s in range(q) if frozenset((s,(s+1)%q))==miss][0]
    A={};B={}
    for a,b in M:
        for j in range(1,q):
            if {a%q,b%q}=={(c+j)%q,(c+j+1)%q}:
                A[j]=a if a%q==(c+j+1)%q else b
                B[j]=b if A[j]==a else a
    seq=[A[j] for j in range(1,q)]+[B[j] for j in range(1,q)]
    if any(seq[i]>=seq[i+1] for i in range(len(seq)-1)): bad+=1
    used=set(x for e in M for x in e)
    for v in range(m):
        if v not in used and not any(adj(v,x) for x in used): extra+=1
def rec(start,chosen,blocked):
    if time.time()-t0>cap: raise TimeoutError
    if len(chosen)==q-1: check(chosen); return
    for k in range(start,len(E)):
        a,b=E[k]
        if a in blocked or b in blocked: continue
        nb=set(blocked)|{a,b}|{x for x in range(m) if adj(a,x) or adj(b,x)}
        chosen.append((a,b)); rec(k+1,chosen,nb); chosen.pop()
try:
    rec(0,[],set()); st="complete"
except TimeoutError: st="TIMEOUT"
print(f"q={q} p={p} n={n}: status={st} induced_(q-1)K2_in_[0,n-2]={cnt} ordering_violations={bad} anticomplete_vertices={extra}",flush=True)
