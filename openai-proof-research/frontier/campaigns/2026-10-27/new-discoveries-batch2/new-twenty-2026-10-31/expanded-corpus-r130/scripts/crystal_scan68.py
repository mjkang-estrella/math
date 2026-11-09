# Scan Corollary 6.8 / Theorem 6.6 of arXiv:2110.15394v2 in A_{n-1}: mu with gaps in [0,D], gamma=lam-mu a nonneg
# combination of simple roots with coefficient sum <= H, lam dominant. Compare KF (Lusztig alternating sum) with
# the number of alpha in S^{id} having phi_i(alpha)=0 for all i (paper's fixed points).
import sys, json, itertools
sys.path.insert(0, __import__('os').path.dirname(__file__))
sys.argv=[sys.argv[0],sys.argv[1],'0']+sys.argv[2:]
import crystal_validate as cv
n=cv.n; D=int(sys.argv[3]); H=int(sys.argv[4])
res=dict(n=n,D=D,H=H,tested=0,fail=0); fails=[]
for gaps in itertools.product(range(D+1),repeat=n-1):
    mu=[sum(gaps[i:]) for i in range(n-1)]+[0]
    for cs in itertools.product(range(H+1),repeat=n-1):
        if sum(cs)==0 or sum(cs)>H: continue
        gam=[0]*n
        for i,cnum in enumerate(cs): gam[i]+=cnum; gam[i+1]-=cnum
        lam=[mu[i]+gam[i] for i in range(n)]
        if any(lam[i]<lam[i+1] for i in range(n-1)): continue
        res['tested']+=1
        a=cv.KF(lam,mu); b=cv.FP(lam,mu)
        if a!=b:
            res['fail']+=1
            if len(fails)<12: fails.append(dict(lam=lam,mu=mu,simple_root_coeffs=list(cs),KF=a,FP=b))
print(json.dumps(dict(res=res,fails=fails)))
