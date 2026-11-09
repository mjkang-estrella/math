import numpy as np, json, sys
from conf_tools import *
res=[]
for p in [5,7,11,13,17,19,23]:
    W=paley(p); assert is_conference(W)
    G,piv=rref_mod(W,p); k=len(piv)
    b=low_weight_search(G,p,k,trials=3000)
    res.append(('paley',p,k,b[0])); print('paley',p,'rank',k,'min found wt',b[0],'MDS bound',p+1-k+1,flush=True)
for m in [3,5,6]:
    p=4*m-1
    Ws=gs_skew(m,limit=40)
    print('GS m=%d n=%d found %d'%(m,4*m,len(Ws)),flush=True)
    seen=set()
    for seqs,W in Ws:
        assert is_conference(W)
        G,piv=rref_mod(W,p); k=len(piv)
        b=low_weight_search(G,p,k,trials=4000)
        print(' ',seqs,'rank',k,'minwt found',b[0],'(MDS d=%d)'%(p+1-k+1),flush=True)
        if b[0]<p+1-k+1:
            print('  COUNTEREXAMPLE codeword coeffs',b[1].tolist(),'word',b[2].tolist())
            np.save('cex_W_%d.npy'%(4*m),W); json.dump({'seqs':seqs,'c_rref':b[1].tolist(),'word':b[2].tolist()},open('cex_%d.json'%(4*m),'w'))
            break
