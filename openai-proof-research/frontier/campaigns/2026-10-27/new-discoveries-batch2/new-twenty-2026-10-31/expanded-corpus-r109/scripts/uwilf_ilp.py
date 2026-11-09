# ILP feasibility: does a uniquely-Wilf class C with C_{<=4} = F (F_3=S_3, given F_4) and containing all
# monotone permutations admit levels 5..N satisfying (k,n)-balance for all k<n<=N and downward closure?
# Infeasible => no infinite uniquely-Wilf class with that F (MathDB 342411). Diagnostic until certified.
import sys, json, itertools, numpy as np, scipy.sparse as sp
from scipy.optimize import milp, LinearConstraint, Bounds
from itertools import permutations, combinations
def std(seq):
    s=sorted(seq); return tuple(s.index(v)+1 for v in seq)
def subpats(p):  # distinct patterns of size len(p)-1
    return {std(p[:i]+p[i+1:]) for i in range(len(p))}
N=int(sys.argv[1]); miss=[tuple(map(int,m)) for m in sys.argv[2:]]  # missing size-4 perms
levels={}
F={1:[(1,)],2:[(1,2),(2,1)],3:list(permutations((1,2,3))),4:[p for p in permutations((1,2,3,4)) if p not in miss]}
allowed={k:set(v) for k,v in F.items()}
for n in range(5,N+1):
    allowed[n]={p for p in permutations(range(1,n+1)) if subpats(p)<=allowed[n-1]}
# containment sets: for each sigma at level n, its distinct k-patterns, computed via iterating subpats
pat={}
for n in range(2,N+1):
    for p in allowed[n]:
        d={n-1:subpats(p)}
        for k in range(n-2,0,-1):
            d[k]=set().union(*(subpats(q) for q in d[k+1]))
        pat[p]=d
var={}; 
for n in range(5,N+1):
    for p in sorted(allowed[n]): var[p]=len(var)
tvar={}
for n in range(5,N+1):
    for k in range(2,n): tvar[(k,n)]=len(var)+len(tvar)
nv=len(var)+len(tvar)
rows=[];lo=[];hi=[]
def add(coefs,l,h): rows.append(coefs);lo.append(l);hi.append(h)
for n in range(5,N+1):
    Mbig=len(allowed[n])
    for k in range(2,n):
        cand=F[k] if k<=4 else sorted(allowed[k])
        for pi in cand:
            c={var[s]:1.0 for s in allowed[n] if pi in pat[s][k]}
            c[tvar[(k,n)]]=-1.0
            if k<=4: add(c,0,0)
            else:
                # sum - t <= M(1-x_pi) and t - sum <= M(1-x_pi)
                c1=dict(c); c1[var[pi]]=c1.get(var[pi],0)+Mbig; add(c1,-np.inf,Mbig)
                c2={j:-v for j,v in c.items()}; c2[var[pi]]=c2.get(var[pi],0)+Mbig; add(c2,-np.inf,Mbig)
    if n>=6:
        for s in allowed[n]:
            for q in pat[s][n-1]: add({var[s]:1.0,var[q]:-1.0},-np.inf,0)
A=sp.lil_matrix((len(rows),nv))
for i,c in enumerate(rows):
    for j,v in c.items(): A[i,j]=v
lb=np.zeros(nv); ub=np.ones(nv)
for k in tvar: ub[tvar[k]]=np.inf
for n in range(5,N+1):
    for m in (tuple(range(1,n+1)),tuple(range(n,0,-1))): lb[var[m]]=1
integrality=np.ones(nv)
r=milp(c=np.zeros(nv),constraints=LinearConstraint(A.tocsr(),lo,hi),bounds=Bounds(lb,ub),integrality=integrality,options={'time_limit':float(sys.argv[0] and 100)})
out={'N':N,'missing':miss,'nvars':nv,'nrows':len(rows),'status':int(r.status),'message':r.message,'sizes':{n:len(allowed[n]) for n in allowed}}
if r.x is not None:
    out['solution_levels']={n:[ ''.join(map(str,p)) for p in sorted(allowed[n]) if r.x[var[p]]>0.5] for n in range(5,N+1)}
print(json.dumps({k:v for k,v in out.items() if k!='solution_levels'}))
if r.x is not None: print({n:len(v) for n,v in out['solution_levels'].items()})
json.dump(out,open(f'outputs/uwilf-N{N}-'+('-'.join(''.join(map(str,m)) for m in miss) or 'S4')+'.json','w'),indent=1)
