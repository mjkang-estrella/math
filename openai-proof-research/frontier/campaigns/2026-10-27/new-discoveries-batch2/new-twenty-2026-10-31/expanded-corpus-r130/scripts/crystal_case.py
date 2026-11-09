# Detailed analysis of the A_4 instance lam=(5,4,4,4,0), mu=(4,4,3,3,3) for arXiv:2110.15394v2.
import sys, json, itertools
sys.path.insert(0, __import__('os').path.dirname(__file__))
from crystal2 import Model
n=5; M=Model(n); lam=[5,4,4,4,0]; mu=[4,4,3,3,3]; rho=[4,3,2,1,0]
def show(x): return None if x is None else ' + '.join((f'{c}' if c>1 else '')+f'({a},{b})' for c,(a,b) in zip(x,M.roots) if c)
# (1) Kostka number by brute-force SSYT count (row-by-row)
def ssyt_count(shape,content):
    # fill rows: row r is weakly increasing, columns strictly increasing; count via recursion over rows
    N=len(content)
    def rows_of_len(L,prev,remaining):
        # generate weakly increasing rows of length L over 1..N with column-strict wrt prev
        def rec(pos,lo,cur,rem):
            if pos==L: yield tuple(cur),rem; return
            lower=max(lo,(prev[pos]+1) if prev is not None else 1)
            for v in range(lower,N+1):
                if rem[v-1]==0: continue
                r=list(rem); r[v-1]-=1
                yield from rec(pos+1,v,cur+[v],r)
        yield from rec(0,1,[],remaining)
    def go(i,prev,rem):
        if i==len(shape): return 1 if all(x==0 for x in rem) else 0
        return sum(go(i+1,row,r) for row,r in rows_of_len(shape[i],prev,rem))
    return go(0,None,list(content))
K1=ssyt_count([5,4,4,4],[4,4,3,3,3])
# (2) S^{id}: alpha with weight lam-mu ; k_i ; fixed points ; components of size-5 alphas
g=[lam[i]-mu[i] for i in range(n)]
k=[lam[i]+rho[i]-lam[i+1]-rho[i+1] for i in range(n-1)]
fps=[]; nonfp=[]
for al in M.kostant(g):
    nz=[i for i in range(1,n) if M.epow(al,i,k[i-1]) is not None]
    (fps if not nz else nonfp).append((al,nz))
out=dict(lam=lam,mu=mu,k=k,kostka_number_ssyt=K1,fixed_points=[dict(alpha=show(a),size=sum(a)) for a,_ in fps],
         non_fixed=[dict(alpha=show(a),size=sum(a),phi_nonzero=nz) for a,nz in nonfp])
# (3) the size-5 alpha with phi_2,phi_3 nonzero: trace both hexagon paths
tr=[]
for a,nz in nonfp:
    if 2 in nz and 3 in nz:
        for name,seq in (('E_2',[2]*k[1]+[3]*(k[1]+k[2])+[2]*k[2]),('E_3',[3]*k[2]+[2]*(k[1]+k[2])+[3]*k[1])):
            x=a; steps=[]
            for j in seq:
                bd=M.BD(x,2,3); y,bl=M.e(x,j)
                steps.append(dict(at=show(x),op=j,BD_at_source=bd,result=show(y),blocked=bl))
                if y is None: break
                x=y
            tr.append(dict(alpha=show(a),path=name,steps=steps))
out['hexagon_traces']=tr
print(json.dumps(out,indent=1))
