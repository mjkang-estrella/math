#!/usr/bin/env python3
"""Exact rational candidate enumeration. No numerical optimizer or external packages."""
import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(50,50))
from fractions import Fraction as F
from itertools import combinations
from functools import cmp_to_key
from math import gcd,lcm
import json
from pathlib import Path

def cross(u,v):return u[0]*v[1]-u[1]*v[0]
def sub(u,v):return (u[0]-v[0],u[1]-v[1])
def dot(u,v):return u[0]*v[0]+u[1]*v[1]
def area(p):return abs(sum(cross(p[i],p[(i+1)%len(p)]) for i in range(len(p))))/F(2)
def normal(u):
 a,b=map(F,u);d=lcm(a.denominator,b.denominator);a,b=int(a*d),int(b*d);g=gcd(a,b);assert g;return a//g,b//g
def half(u):return int(u[1]<0 or (u[1]==0 and u[0]<0))
def cmp(u,v):
 if half(u)!=half(v):return half(u)-half(v)
 return -((cross(u,v)>0)-(cross(u,v)<0))
def supports(p,ns):return [(n,max(dot(n,v) for v in p)) for n in ns]
def intersect(a,b):
 (u,h),(v,k)=a,b;d=cross(u,v)
 if not d:return None
 return F(h*v[1]-u[1]*k,d),F(u[0]*k-h*v[0],d)
def candidate(lines):
 lines=sorted(lines,key=cmp_to_key(lambda a,b:cmp(a[0],b[0])))
 if any(cross(lines[i][0],lines[(i+1)%len(lines)][0])<=0 for i in range(len(lines))):return None
 q=[intersect(lines[i],lines[(i+1)%len(lines)]) for i in range(len(lines))]
 if any(dot(n,v)>h for n,h in lines for v in q):return None
 return area(q),q

def enumerate_chord(p):
 ns=set()
 for a,b in combinations(p,2):
  d=sub(b,a);n=normal((d[1],-d[0]));ns.add(n);ns.add((-n[0],-n[1]))
 lines=supports(p,sorted(ns,key=cmp_to_key(cmp)))
 best=None;count=0;ties=0
 for k in [3,4]:
  for ls in combinations(lines,k):
   c=candidate(ls)
   if c is None:continue
   count+=1
   if best is None or c[0]<best[0]:best=(c[0],c[1],ls);ties=1
   elif c[0]==best[0]:ties+=1
 assert best
 return {'area':best[0],'ratio':best[0]/area(p),'vertices':best[1],'lines':best[2],'candidates':count,'ties':ties,'normals':len(ns)}

def midpoint_cut(p):
 # Construct witnesses, not a claimed exhaustive ordinary quadrilateral solver.
 edges=[]
 for i,a in enumerate(p):
  d=sub(p[(i+1)%len(p)],a);n=normal((d[1],-d[0]));edges.append((n,dot(n,a)))
 best=None
 for es in combinations(edges,3):
  for i,j in combinations(range(3),2):
   o=intersect(es[i],es[j])
   if o is None:continue
   u=(-es[i][0][1],es[i][0][0]);w=(-es[j][0][1],es[j][0][0]);d=cross(u,w)
   for v in p:
    z=sub(v,o);a=F(cross(z,w),d);b=F(cross(u,z),d)
    x=(o[0]+2*a*u[0],o[1]+2*a*u[1]);y=(o[0]+2*b*w[0],o[1]+2*b*w[1]);z=sub(y,x)
    if z==(0,0):continue
    n=normal((z[1],-z[0]))
    for n in [n,(-n[0],-n[1])]:
     h=dot(n,v)
     if any(dot(n,t)>h for t in p):continue
     c=candidate(list(es)+[(n,h)])
     if c and (best is None or c[0]<best[0]):best=(c[0],c[1],list(es)+[(n,h)],v)
 assert best
 return best

def encode(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
 if isinstance(x,(list,tuple)):return [encode(v) for v in x]
 return x

def main():
 p=[(0,5),(-5,1),(-3,-4),(3,-4),(5,2)]
 assert all(cross(sub(p[(i+1)%5],p[i]),sub(p[(i+2)%5],p[(i+1)%5]))>0 for i in range(5))
 result=enumerate_chord(p);q=midpoint_cut(p)
 assert result['area']==F(2781,35) and result['ratio']==F(1854,1435)
 assert q[0]==F(873,11) and result['area']-q[0]==F(36,385)
 assert q[0]<result['area']
 assert 5*result['ratio']**2<9 # strictly below the source conjectural bound
 # A short cut at q's nonchord support vertex introduces the missing direction.
 ns={n for n,h in result['lines']}
 allns=set()
 for a,b in combinations(p,2):
  d=sub(b,a);n=normal((d[1],-d[0]));allns.update([n,(-n[0],-n[1])])
 new=[(n,h) for n,h in q[2] if n not in allns];assert len(new)==1
 n,h=new[0];v=q[3];idx=p.index(v);a=p[(idx-1)%5];b=p[(idx+1)%5]
 eps=F(1,100)
 def cutpoint(w):
  t=eps/(h-dot(n,w));assert 0<t<1
  return (F(v[0])+t*(w[0]-v[0]),F(v[1])+t*(w[1]-v[1]))
 x,y=cutpoint(a),cutpoint(b)
 pp=p[:idx]+[x,y]+p[idx+1:]
 assert dot(n,x)==dot(n,y)==h-eps
 assert area(pp)==area(p)-F(5,1386)*eps**2
 # q remains a chord quadrilateral of pp: its three original edge directions survive;
 # its fourth direction is now the new small edge.
 dirs={normal((sub(t,s)[1],-sub(t,s)[0])) for s,t in combinations(pp,2)}
 dirs |= {(-a,-b) for a,b in list(dirs)}
 assert all(nn in dirs for nn,hh in q[2])
 assert all(dot(nn,t)<=hh for nn,hh in q[2] for t in pp)
 out={'status':'PASS','polygon':p,'polygon_area':area(p),'chord_minimum':result,
      'ordinary_witness':q,'new_normal':n,'cut_support_offset':eps,'cut_polygon':pp,
      'cut_polygon_area':area(pp),'cut_ratio_upper_bound':q[0]/area(pp),
      'gap_at_limit':result['area']-q[0],
      'meaning':'Exact obstruction to continuity-based polygon reduction; NOT a counterexample to Conjecture 2.2.'}
 (Path(__file__).parent/'checks.json').write_text(json.dumps(encode(out),indent=2)+'\n')
 print(json.dumps(encode(out),indent=2))
if __name__=='__main__':main()
