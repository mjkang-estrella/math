"""Deterministic finite enumeration + floating Gibbs diagnostics; not a proof."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import json,math,itertools
import numpy as np
import networkx as nx
from scipy.special import logsumexp,xlogy
from scipy.optimize import minimize
OUT=Path(__file__).parent

def matchings(n,edges):
 adj=[[] for _ in range(n)]
 for i,(u,v) in enumerate(edges):
  assert u!=v
  adj[u].append((v,i));adj[v].append((u,i))
 def rec(mask):
  if not mask:yield ();return
  u=(mask&-mask).bit_length()-1
  for v,i in adj[u]:
   if mask>>v&1:
    for rest in rec(mask^(1<<u)^(1<<v)):yield (i,)+rest
 return list(rec((1<<n)-1))

def matrix(n,edges):
 ms=matchings(n,edges);A=np.zeros((len(ms),len(edges)))
 for i,M in enumerate(ms):A[i,list(M)]=1
 return ms,A

def evaluate(A,t):
 z=A@t;logz=logsumexp(z);p=np.exp(z-logz);x=p@A
 H=-np.sum(xlogy(p,p));F=-np.sum(xlogy(x,x));B=-np.sum(xlogy(1-x,1-x))
 return (F-H)/B if B>1e-10 else 0.,H,F,B,x,p

def optimize(A,t,maxiter=90):
 def fun(t):
  R,H,F,B,x,p=evaluate(A,t);xx=np.clip(x,1e-12,1-1e-12)
  g=-np.log(xx)-1+t-R*(np.log1p(-xx)+1)
  Ag=A@g;grad=A.T@(p*(Ag-p@Ag))/max(B,1e-10)
  return -R,-grad
 r=minimize(fun,t,jac=True,method='L-BFGS-B',bounds=[(-18,18)]*A.shape[1],options={'maxiter':maxiter,'ftol':1e-12})
 return r.x

def expand(n,edges,v):
 ports=[i for i,e in enumerate(edges) if v in e]
 assert len(ports)==3
 ee=list(edges);tri=[v,n,n+1]
 for j,i in enumerate(ports):
  u,w=ee[i];ee[i]=(tri[j],w if u==v else u)
 ee += [(tri[1],tri[2]),(tri[0],tri[2]),(tri[0],tri[1])]
 return n+2,ee

def main():
 rng=np.random.default_rng(250910);cases=[]
 for i,g in enumerate(nx.graph_atlas_g()):
  n=len(g)
  if n in [2,4,6] and nx.is_connected(g):cases.append((f'atlas-{i}',n,list(g.edges()),True))
 for n in [8,10,12]:
  cases.append((f'complete-{n}',n,list(nx.complete_graph(n).edges()),True))
  for d in range(3,min(8,n)):
   for seed in range(10):
    g=nx.random_regular_graph(d,n,seed=2500+100*n+10*d+seed);cases.append((f'reg-{n}-{d}-{seed}',n,list(g.edges()),seed<2))
 for n in [14,16,18]:
  for d in [3,4,5]:
   for seed in range(5):
    g=nx.random_regular_graph(d,n,seed=251000+100*n+10*d+seed);cases.append((f'reg-{n}-{d}-{seed}',n,list(g.edges()),False))
 for name,g in [('petersen',nx.petersen_graph()),('octahedron',nx.octahedral_graph()),('cube',nx.cubical_graph()),('dodecahedron',nx.dodecahedral_graph())]:cases.append((name,len(g),list(g.edges()),True))
 for depth in range(2,8):
  n=2;ee=[(0,1)]*3
  for k in range(depth):n,ee=expand(n,ee,0)
  cases.append((f'klee-{depth}',n,ee,True))
 # Fourfold parallel selector, fixed-edge boundary, and duplicated Klee edges.
 cases.append(('parallel-four',2,[(0,1)]*4,True))
 n=2;ee=[(0,1)]*3
 for k in range(5):n,ee=expand(n,ee,0)
 cases.append(('klee-parallel',n,ee+ee[::3],True))
 best=[];records=[];nc=0
 for name,n,ee,opt in cases:
  ms,A=matrix(n,ee)
  if not ms:continue
  ts=[np.zeros(len(ee))]+[rng.normal(0,s,len(ee)) for s in [.25,1,3,8]]
  if opt:ts += [optimize(A,ts[j]) for j in [0,2]]
  vals=[]
  for t in ts:
   R,H,F,B,x,p=evaluate(A,t);nc+=1
   vals.append((R,t,H,F,B,x))
  R,t,H,F,B,x=max(vals,key=lambda z:z[0])
  record=dict(name=name,n=n,s=len(ee),N=len(ms),ratio=float(R),H=float(H),F=float(F),B=float(B),optimized=opt)
  records.append(record)
  best.append((R,dict(record,edges=ee,theta=t.tolist(),x=x.tolist())))
  if len(records)%50==0:print(len(records),'graphs',nc,'laws best',max(z[0] for z in best),flush=True)
 best.sort(key=lambda z:-z[0]);result={'seed':250910,'graphs':len(records),'gibbs_laws':nc,'limitations':'Float64 optimization with clipped gradient only; exact combinatorial enumeration, no global optimization certificate. Positive weights may underflow in extreme coordinates; no numerical result is a proof.','records':records,'top': [v for _,v in best[:15]]}
 (OUT/'search-results.json').write_text(json.dumps(result,indent=2)+'\n');print('DONE',len(records),nc,[(r['name'],r['ratio']) for _,r in best[:8]],flush=True)
if __name__=='__main__':main()
