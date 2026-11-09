from pathlib import Path
import json,itertools as it
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
D=Path(__file__).resolve().parents[1]
x=json.loads((D/'outputs/edgepatterns.json').read_text())[0]['failures'][0];adj=x['adj'];layers=x['layers'];mis=[]
for s in range(1<<len(adj)):
 if all(not(s>>i&1) or not(adj[i]&s) for i in range(len(adj))):
  if not mis or s.bit_count()>mis[0].bit_count():mis=[s]
  elif s.bit_count()==mis[0].bit_count():mis.append(s)
e=[F(sum(sum(1 for i,l in enumerate(layers) if l==k and s>>i&1) for s in mis),len(mis)) for k in range(3)]
# independently enumerate every tree through all labeled leaf-count sequences (3^4).
T=set();cert=[]
for seq in it.product(range(3),repeat=4):
 edges=[(0,1),(0,2),(0,3),(1,4),(1,5)];lay=[0,0,1,1,1,1]
 for par,num in zip(range(2,6),seq):
  for _ in range(num):edges.append((par,len(lay)));lay.append(2)
 ind=[]
 for s in range(1<<len(lay)):
  if all(not(s>>a&1 and s>>b&1) for a,b in edges):
   if not ind or s.bit_count()>ind[0].bit_count():ind=[s]
   elif s.bit_count()==ind[0].bit_count():ind.append(s)
 t=tuple(F(sum(sum(1 for i,l in enumerate(lay) if l==k and s>>i&1) for s in ind),len(ind)) for k in range(3));T.add(t);cert.append(dict(seq=seq,e=[str(v) for v in t],mis_count=len(ind)))
A=np.array([[-float(v) for v in t] for t in T]);r=linprog([float(v) for v in e],A_ub=A,b_ub=[-1]*len(T),bounds=(0,None),method='highs',options={'threads':1})
alpha=[F(float(v)).limit_denominator(100000) for v in r.x]
print('e',e,'MIS',mis,'alpha',alpha,'alphaP',sum(a*b for a,b in zip(alpha,e)),'minTree',min(sum(a*b for a,b in zip(alpha,t)) for t in T))
obj=dict(graph=x,mis=mis,e=[str(v) for v in e],alpha=[str(v) for v in alpha],alphaP=str(sum(a*b for a,b in zip(alpha,e))),minTree=str(min(sum(a*b for a,b in zip(alpha,t)) for t in T)),trees=cert)
(D/'outputs/edge-certificate.json').write_text(json.dumps(obj,indent=2)+'\n')
