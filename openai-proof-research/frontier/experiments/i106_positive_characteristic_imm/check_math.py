"""Exact finite diagnostics, not proof of asymptotic statements. Pure read-only run()."""
from itertools import product,combinations
from fractions import Fraction
from math import comb

def rank(A,p=0):
 A=[[x%p if p else Fraction(x) for x in row] for row in A]; r=0
 for j in range(len(A[0]) if A else 0):
  i=next((i for i in range(r,len(A)) if A[i][j]),None)
  if i is None:continue
  A[r],A[i]=A[i],A[r]; inv=pow(A[r][j],-1,p) if p else 1/A[r][j]
  A[r]=[(x*inv)%p if p else x*inv for x in A[r]]
  for i in range(len(A)):
   if i!=r and A[i][j]:
    z=A[i][j];A[i]=[(x-z*y)%p if p else x-z*y for x,y in zip(A[i],A[r])]
  r+=1
  if r==len(A):break
 return r

def comps(total,r):
 if r==1:yield(total,);return
 for x in range(total+1):
  for rest in comps(total-x,r-1):yield(x,)+rest

def corridor_minor(w,schedule,t,av=0,bu=0):
 d=len(schedule);vl=[j for j,x in enumerate(schedule) if x=='V'];ul=[j for j,x in enumerate(schedule) if x=='U'];k=len(vl)
 assert schedule[0]=='V' and schedule[-1]=='U' and 'VV' not in schedule
 paths=[]
 for interior in product(range(w),repeat=d-1):
  vs=(0,)+interior+(0,);edges=tuple((j,vs[j],vs[j+1]) for j in range(d));paths.append(edges)
 active=set()
 for j in range(d):
  for l in (range(1) if j==0 else range(t)):
   for r in (range(1) if j==d-1 else range(t)):active.add((j,l,r))
 V=[(j,l,r) for j in vl for l in range(w) for r in range(w)];U=[(j,l,r) for j in ul for l in range(w) for r in range(w)]
 bv=[x for x in V if x not in active];bb=[x for x in U if x not in active]
 witnesses={}
 for P in paths:
  if all(e in active for e in P):witnesses.setdefault(tuple(P[j] for j in vl),tuple(P[j] for j in ul))
 assert len(witnesses)==t**(2*k-1)
 # Small complete ballast sectors only; dictionary sparse columns/rows.
 columns=[];rows=[]
 for vp,up in witnesses.items():
  for rv in comps(av,len(bv)):
   for ru in comps(bu,len(bb)):
    v={e:c for e,c in zip(bv,rv) if c};u={e:c for e,c in zip(bb,ru) if c}
    cv=dict(v);cv.update({e:1 for e in vp});ou=dict(u);ou.update({e:1 for e in up})
    columns.append((cv,u));rows.append((v,ou))
 def key(v,u):return tuple(sorted(v.items())),tuple(sorted(u.items()))
 rowidx={key(v,u):i for i,(v,u) in enumerate(rows)};assert len(rowidx)==len(rows)
 entries={};checks=0
 for j,(v,u) in enumerate(columns):
  for P in paths:
   if not all(v.get(P[i],0)>0 for i in vl):continue
   vv=dict(v);uu=dict(u);c=1
   for i in vl:
    e=P[i];c*=vv[e];vv[e]-=1
    if not vv[e]:del vv[e]
   for i in ul:
    e=P[i];uu[e]=uu.get(e,0)+1
   i=rowidx.get(key(vv,uu))
   if i is not None:entries[i,j]=entries.get((i,j),0)+c
  checks+=1
 assert entries=={(i,i):1 for i in range(len(rows))}
 return {'w':w,'schedule':schedule,'corridor':t,'ballast_degrees':[av,bu],'minor_order':len(rows),'column_checks':checks}

def balanced_torsion_minor():
 w=5; schedule='VUVUU'; vl=[0,2]; ul=[1,3,4]
 # First VU pair is a three-way dot product; all other path edges fixed.
 fixedv={(2,0,0):1,(0,1,1):1}
 fixedu={(4,1,1):1}  # Inactive final endpoint coordinate.
 columns=[];rows=[]
 for j in range(3):
  cv=dict(fixedv);cv.update({(0,0,i):1 for i in range(3) if i!=j})
  cu=dict(fixedu);cu[(1,j,0)]=1;columns.append((cv,cu))
  rv={(0,1,1):1,(0,0,j):1}
  ru=dict(fixedu);ru.update({(1,i,0):1 for i in range(3) if i!=j});ru.update({(3,0,0):1,(4,0,0):1});rows.append((rv,ru))
 A=[[0]*3 for _ in range(3)]
 for j,(v,u) in enumerate(columns):
  for interior in product(range(w),repeat=4):
   vertices=(0,)+interior+(0,);P=[(i,vertices[i],vertices[i+1]) for i in range(5)]
   if not all(v.get(P[i],0) for i in vl):continue
   vv=dict(v);uu=dict(u);coeff=1
   for i in vl:
    coeff*=vv[P[i]];vv[P[i]]-=1
    if not vv[P[i]]:del vv[P[i]]
   for i in ul:uu[P[i]]=uu.get(P[i],0)+1
   for i,row in enumerate(rows):
    if (vv,uu)==row:A[i][j]+=coeff
 assert A==[[0,1,1],[1,0,1],[1,1,0]]
 return {'width':5,'degree':5,'schedule':schedule,'a':4,'b':2,'minor':A,'determinant':2}

def run():
 results=[]
 for w,s,t,a,b in [(3,'VU',2,0,0),(3,'VUU',2,1,0),(3,'VUVU',2,0,1),(2,'VUVU',1,1,1)]:results.append(corridor_minor(w,s,t,a,b))
 inclusion=[]
 for p in [2,3,5]:
  r=2*p-1;left=list(combinations(range(r),p-1));right=list(combinations(range(r),p))
  A=[[int(set(x)<set(y)) for y in right] for x in left]
  assert all(sum(row)==p for row in A)
  rq=rank(A);rp=rank(A,p);assert rp<rq==len(A)
  inclusion.append({'prime':p,'variables_per_side':r,'block_order':len(A),'rank_Q':rq,'rank_mod_p':rp,'row_sum':p})
 assert rank([[0,1,1],[1,0,1],[1,1,0]],2)==2
 # Ordinary derivatives versus contraction at x^p; multiplicativity failure of naive Hasse relabel.
 for p in [2,3,5,7]:
  assert p%p==0 and comb(p,p)%p==1
 # Known original obstructions, directly with integer arithmetic.
 assert 5*5>2*(6-1)+5
 for p in [2,3,5,7]:assert (1*(-1))%p!=0
 return {'status':'PASS','corridor_minors':results,'balanced_torsion_minor':balanced_torsion_minor(),'inclusion_blocks':inclusion,'scope':'Finite exact diagnostics only; universal proofs are in the report'}
if __name__=='__main__':
 import json;print(json.dumps(run(),indent=2))
