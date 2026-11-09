"""Tableau reconstruction via minors (Erickson-Herden-Meddaugh-Sepanski-Hammon arXiv:2307.13161).
T - m: delete cell m, slide smaller of right/below neighbour into the gap until gap is an outer corner, remove gap, decrement entries > m.
A_s[T][T'] = #{m : T - m = T'}.  Multiset of k-minors of T = row T of A_n A_{n-1} ... A_{n-k+1};  set = support of that row.
Usage: minors.py NMAX  -> for each n<=NMAX, k<n: report whether T -> mM_k(T) and T -> M_k(T) are injective on YT(n)."""
import sys, numpy as np
def gen(nmax):
    levels=[[()]]
    for s in range(1,nmax+1):
        out=[]
        for T in levels[-1]:
            rows=[list(r) for r in T]
            for i in range(len(rows)+1):
                if i==len(rows) or (i==0 or len(rows[i])<len(rows[i-1])):
                    if i<len(rows) and i>0 and len(rows[i])>=len(rows[i-1]): continue
                    R=[r[:] for r in rows]
                    if i==len(R): R.append([s])
                    else: R[i].append(s)
                    out.append(tuple(tuple(r) for r in R))
        levels.append(sorted(set(out)))
    return levels
def delete(T,m):
    R=[list(r) for r in T]
    for i,r in enumerate(R):
        if m in r: ci=i; cj=r.index(m); break
    i,j=ci,cj
    while True:
        right=R[i][j+1] if j+1<len(R[i]) else None
        below=R[i+1][j] if i+1<len(R) and j<len(R[i+1]) else None
        if right is None and below is None: break
        if below is None or (right is not None and right<below): R[i][j]=right; j+=1
        else: R[i][j]=below; i+=1
    del R[i][j]
    if not R[i]: del R[i]
    return tuple(tuple(x-1 if x>m else x for x in r) for r in R)
def main():
    nmax=int(sys.argv[1]); L=gen(nmax); idx=[{T:i for i,T in enumerate(l)} for l in L]
    print('SYT counts',[len(l) for l in L],flush=True)
    A=[None,None]
    for s in range(2,nmax+1):
        a=np.zeros((len(L[s]),len(L[s-1])),dtype=np.int64)
        for t,T in enumerate(L[s]):
            for m in range(1,s+1): a[t,idx[s-1][delete(T,m)]]+=1
        A.append(a)
    for n in range(2,nmax+1):
        M=None
        res=[]
        for k in range(1,n):
            M=A[n] if M is None else M@A[n-k+1]
            dm=len({r.tobytes() for r in M}); ds=len({(r>0).tobytes() for r in M})
            res.append(f'k={k}:multi{"OK" if dm==len(L[n]) else "x"+str(len(L[n])-dm)} set{"OK" if ds==len(L[n]) else "x"+str(len(L[n])-ds)}')
        print('n=',n,' '.join(res),flush=True)
if __name__=='__main__': main()
