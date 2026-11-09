# Exhaustive MDS test: code C(W) over F_p is MDS (dim k) iff every k-subset of columns of an
# rref generator G is nonsingular. Batched modular Gaussian elimination.
import numpy as np, itertools, json, sys
from conf_tools import *
def batched_singular(Ms,p):
    M=Ms.copy()%p; B,k,_=M.shape; sing=np.zeros(B,bool)
    for c in range(k):
        col=M[:,c:,c]; nz=col!=0
        has=nz.any(1); sing|=~has
        piv=np.argmax(nz,1)+c
        idx=np.arange(B)
        rowp=M[idx,piv].copy(); rowc=M[idx,c].copy(); M[idx,piv]=rowc; M[idx,c]=rowp
        pv=M[:,c,c]; inv=np.array([pow(int(x),p-2,p) if x else 0 for x in range(p)])[pv]
        M[:,c,:]=(M[:,c,:]*inv[:,None])%p
        f=M[:,c+1:,c]
        M[:,c+1:,:]=(M[:,c+1:,:]-f[:,:,None]*M[:,c,None,:])%p
    return sing
def bad_subsets(W,p,size=None):
    G,piv=rref_mod(W,p); k=len(piv); n=G.shape[1]; size=size or k
    subs=np.array(list(itertools.combinations(range(n),k)))
    bad=0; ex=None
    for s in range(0,len(subs),50000):
        S=subs[s:s+50000]; Ms=G[:,S].transpose(1,0,2)  # B x k x k
        sg=batched_singular(Ms,p); bad+=int(sg.sum())
        if ex is None and sg.any(): ex=S[np.argmax(sg)].tolist()
    return k,bad,ex
if __name__=='__main__':
    out={}
    for p in [11,19]:
        W=paley(p); k,b,ex=bad_subsets(W,p); print('paley',p,'k',k,'singular k-subsets',b,flush=True); out['paley%d'%p]=b
    m=int(sys.argv[1]) if len(sys.argv)>1 else 5; p=4*m-1
    Ws=gs_skew(m)
    print('GS order',4*m,'matrices',len(Ws),flush=True)
    res=[]
    for seqs,W in Ws:
        k,b,ex=bad_subsets(W,p); res.append({'seqs':seqs,'k':k,'singular_k_subsets':b,'example':ex})
        print(seqs,k,b,ex,flush=True)
    out['gs']=res; json.dump(out,open('exhaustive_mds_m%d.json'%m,'w'),indent=1)
