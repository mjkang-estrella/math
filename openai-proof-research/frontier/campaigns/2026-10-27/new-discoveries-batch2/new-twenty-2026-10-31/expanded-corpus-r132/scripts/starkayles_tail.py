# Describe the period-12 tails of S(j,.) relative to the Kayles tail.
import sys,json
import numpy as np
sys.argv=[sys.argv[0]]+sys.argv[1:]
exec(open(__file__.rsplit('/',1)[0]+'/starkayles_np.py').read().split("S={0:K.copy()}")[0])
J1=int(sys.argv[2]); L=int(sys.argv[3])
prev=[K.copy()]
res={}
for j in range(1,J1+1):
    Sj=np.zeros(L+1,dtype=np.int64); Sj[0]=j
    lower=np.array(prev)
    for l in range(1,L+1):
        parts=[lower[:,l], (np.arange(j+1))^K[l-1]]
        if l>1:
            i=np.arange(1,l)
            parts+= [Sj[i-1]^K[l-i], Sj[i]^K[l-i-1], Sj[i-1]^K[l-i-1]]
        parts.append(np.array([Sj[l-1]]))
        allv=np.concatenate(parts); size=int(allv.max())+2
        seen=np.zeros(size,bool); seen[allv]=True; Sj[l]=int(np.argmin(seen))
    prev.append(Sj)
    tail=Sj[L-23:L+1-12]; kt=K[L-23:L+1-12]
    shifts={}
    for s in range(12):
        x=Sj[L-11:L+1]^K[L-11-s:L+1-s]
        if len(set(x.tolist()))==1: shifts[s]=int(x[0])
    res[j]={'tail':Sj[L-11:L+1].tolist(),'xor_const_shift':shifts}
    print(j,res[j],flush=True)
