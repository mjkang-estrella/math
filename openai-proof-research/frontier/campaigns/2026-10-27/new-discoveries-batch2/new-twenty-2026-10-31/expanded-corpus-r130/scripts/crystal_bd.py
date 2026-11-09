# MathDB 352401 / arXiv:2110.15394v2 Conjecture 5.5 search with the independent implementation crystal2.py.
# For each Kostant partition alpha (sizes <= S) in A_{n-1}, each i with i,i+1 in I, each admissible (k_i,k_{i+1})
# (k_j = g_j + 1 + d_j, d_j >= 0 from dominant mu; g = weight of alpha), with phi_i(alpha), phi_{i+1}(alpha) != 0,
# walk E_i = e_i^{k_{i+1}} e_{i+1}^{k_i+k_{i+1}} e_i^{k_i} (alpha) and E_{i+1} = e_{i+1}^{k_i} e_i^{k_i+k_{i+1}} e_{i+1}^{k_{i+1}} (alpha)
# and record every edge x -> e_j(x) on the walk whose source x exhibits Exception BD for {i,i+1}.
import sys, json, itertools
sys.path.insert(0, __import__('os').path.dirname(__file__))
from crystal2 import Model
n=int(sys.argv[1]); S=int(sys.argv[2]); M=Model(n)
def all_kp(size):
    R=len(M.roots)
    def comps(t,k):
        if k==1: yield (t,); return
        for a in range(t+1):
            for r in comps(t-a,k-1): yield (a,)+r
    yield from comps(size,R)
stats=dict(n=n,maxsize=S,alphas=0,instances=0,viol_instances=0,viol_full_path_nonzero=0,viol_in_first_segment=0)
examples=[]
for size in range(1,S+1):
    for al in all_kp(size):
        stats['alphas']+=1; g=M.weight(al)
        for i in range(1,n-1):
            eps_i=0; x=al
            while True:
                x,_b=M.e(x,i)
                if x is None: break
                eps_i+=1
            eps_j=0; x=al
            while True:
                x,_b=M.e(x,i+1)
                if x is None: break
                eps_j+=1
            gi=g[i-1]-g[i]; gj=g[i]-g[i+1]
            for ki in range(max(1,gi+1),eps_i+1):
                for kj in range(max(1,gj+1),eps_j+1):
                    stats['instances']+=1
                    for name,seq in (('E_i',[i]*ki+[i+1]*(ki+kj)+[i]*kj),('E_i+1',[i+1]*kj+[i]*(ki+kj)+[i+1]*ki)):
                        x=al; hits=[]; died=None
                        for step,j in enumerate(seq):
                            if M.BD(x,i,i+1): hits.append(dict(step=step,vertex=x,next_op=j))
                            y,bl=M.e(x,j)
                            if y is None: died=dict(step=step,op=j,blocked=bl); break
                            x=y
                        if hits:
                            stats['viol_instances']+=1
                            first_len=ki if name=='E_i' else kj
                            if died is None: stats['viol_full_path_nonzero']+=1
                            if any(h['step']<first_len for h in hits): stats['viol_in_first_segment']+=1
                            if len(examples)<6: examples.append(dict(alpha={f'{a},{b}':c for c,(a,b) in zip(al,M.roots) if c},i=i,k_i=ki,k_i1=kj,path=name,hits=[dict(step=h['step'],next_op=h['next_op'],vertex={f'{a},{b}':c for c,(a,b) in zip(h['vertex'],M.roots) if c}) for h in hits],died=died))
    print(json.dumps(dict(size=size,**stats)),flush=True)
print(json.dumps(dict(final=stats,examples=examples)))
