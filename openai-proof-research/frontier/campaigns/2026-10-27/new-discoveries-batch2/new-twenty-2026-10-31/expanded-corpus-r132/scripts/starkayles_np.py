# Vectorised version of starkayles.py (same recursion); prints minimal eventual period and pre-period per j.
import sys,json
import numpy as np
J0=int(sys.argv[1]); J1=int(sys.argv[2]); L=int(sys.argv[3])
K=np.zeros(L+1,dtype=np.int64)
for n in range(1,L+1):
    a=np.arange(n); vals=K[a]^K[n-1-a]
    b=np.arange(n-1); vals2=K[b]^K[n-2-b] if n>=2 else np.zeros(0,dtype=np.int64)
    seen=np.zeros(256,bool); seen[vals]=True; seen[vals2]=True
    K[n]=int(np.argmin(seen))
def mex(arr,size):
    seen=np.zeros(size,bool); seen[arr[arr<size]]=True
    return int(np.argmin(seen)) if not seen.all() else size
def period(seq):
    n=len(seq)
    for p in range(1,n//4):
        d=np.nonzero(seq[:n-p]!=seq[p:])[0]
        n0=int(d[-1])+1 if len(d) else 0
        if n-n0>=3*p+50 and n0<=n//2: return p,n0
    return None
S={0:K.copy()}
out={'L':L,'kayles':period(K)}
prev=[K.copy()]
for j in range(1,J1+1):
    Sj=np.zeros(L+1,dtype=np.int64); Sj[0]=j
    lower=np.array([pv for pv in prev]) # rows j-1..0 order: prev[t]=S[t]
    for l in range(1,L+1):
        parts=[lower[:,l], (np.arange(j+1))^K[l-1]]
        if l>1:
            i=np.arange(1,l)
            parts+= [Sj[i-1]^K[l-i], Sj[i]^K[l-i-1], Sj[i-1]^K[l-i-1]]
        parts.append(np.array([Sj[l-1]]))
        allv=np.concatenate(parts)
        Sj[l]=mex(allv,int(allv.max())+2)
    prev.append(Sj)
    if j>=J0:
        out[j]={'period':period(Sj),'max':int(Sj.max())}
        print(j,out[j],flush=True)
