"""Pure exact finite diagnostics. No universal mathematical certification."""
from itertools import product,combinations
from math import comb
from fractions import Fraction

def comps(a,r):
 if r==0:
  if a==0:yield ()
  return
 if r==1:yield (a,);return
 for i in range(a+1):
  for z in comps(a-i,r-1):yield (i,)+z

def rank(A,p):
 A=[[x%p for x in row] for row in A];r=0
 for j in range(len(A[0]) if A else 0):
  z=next((i for i in range(r,len(A)) if A[i][j]),None)
  if z is None:continue
  A[r],A[z]=A[z],A[r];inv=pow(A[r][j],-1,p);A[r]=[x*inv%p for x in A[r]]
  for i in range(r+1,len(A)):
   if A[i][j]:
    c=A[i][j];A[i]=[(x-c*y)%p for x,y in zip(A[i],A[r])]
  r+=1
  if r==len(A):break
 return r

def geometry(w,schedule):
 V=[(j,l,r) for j,z in enumerate(schedule) if z=='V' for l in range(w) for r in range(w)]
 U=[(j,l,r) for j,z in enumerate(schedule) if z=='U' for l in range(w) for r in range(w)]
 paths=[]
 for ints in product(range(w),repeat=len(schedule)-1):
  pts=(0,)+ints+(0,);paths.append(tuple((j,pts[j],pts[j+1]) for j in range(len(schedule))))
 return V,U,paths

def periodic(w,s,t,L,av,bu):
 V,U,paths=geometry(w,s);active={e for e in V+U if e[1]<t and e[2]<t and (e[0]!=0 or e[1]==0) and (e[0]!=len(s)-1 or e[2]==0)}
 witnesses={}
 for P in paths:
  if set(P)<=active:witnesses.setdefault(tuple(e for e in P if e in V),tuple(e for e in P if e in U))
 def baselines(vars,degree):
  return [c for c in comps(degree,len(vars)) if all(c[i]%L==0 for i,e in enumerate(vars) if e in active)]
 vb=baselines(V,av);ub=baselines(U,bu);cols=[];rows=[]
 for vp,up in witnesses.items():
  q=tuple(int(e in vp) for e in V);z=tuple(int(e in up) for e in U)
  for a in vb:
   for b in ub:cols.append((tuple(i+j for i,j in zip(a,q)),b));rows.append((a,tuple(i+j for i,j in zip(b,z))))
 idx={z:i for i,z in enumerate(rows)};assert len(idx)==len(rows)==len(set(cols))
 ordinary=[]
 for j,(a,b) in enumerate(cols):
  found={};ordfound={}
  for P in paths:
   pv=[V.index(e) for e in P if e in V];pu=[U.index(e) for e in P if e in U]
   if any(a[i]==0 for i in pv):continue
   aa=list(a);bb=list(b);c=1
   for i in pv:c*=aa[i];aa[i]-=1
   for i in pu:bb[i]+=1
   i=idx.get((tuple(aa),tuple(bb)))
   if i is not None:found[i]=found.get(i,0)+1;ordfound[i]=ordfound.get(i,0)+c
  assert found=={j:1};assert set(ordfound)=={j};assert ordfound[j]%L==1;ordinary.append(ordfound[j])
 return {'width':w,'schedule':s,'t':t,'period':L,'baseline_degrees':[av,bu],'minor_order':len(rows),'largest_ordinary_diagonal':max(ordinary)}

def local_sector(h,p):
 levels={}
 for eta in product(*(range(x+1) for x in h)):levels.setdefault(sum(eta),[]).append(eta)
 ranks={}
 for e,cols in levels.items():
  rows=levels.get(e+1,[]);idx={v:i for i,v in enumerate(rows)};A=[[0]*len(cols) for _ in rows]
  for j,eta in enumerate(cols):
   for i in range(len(h)):
    if eta[i]<h[i]:z=list(eta);z[i]+=1;A[idx[tuple(z)]][j]+=1
  ranks[e]=rank(A,p)
 return levels,ranks

def local_rank(t,d,e,p):
 total=0
 for h in comps(d+e,t):total+=local_sector(h,p)[1][e]
 return total

def excursion_formula(w,s,t,a,b,p):
 k=s.count('V');v=k*w*w;u=s.count('U')*w*w
 states={(0,0):1}
 for _ in range(k):
  new={}
  for (A,B),c in states.items():
   for d in range(1,a-A+1):
    for e in range(b-B+1):
     r=local_rank(t,d,e,p)
     if r:new[A+d,B+e]=new.get((A+d,B+e),0)+c*r
  states=new
 def h(r,d):return comb(r+d-1,d) if r else int(d==0)
 return sum(c*h(v-k*t,a-A)*h(u-k*t,b-B) for (A,B),c in states.items())

def excursion_actual(w,s,t,a,b,p):
 V,U,paths=geometry(w,s);allowed=set();j=0
 while j<len(s):
  assert s[j]=='V';allowed.update((j,0,l) for l in range(t));allowed.update((j+1,l,0) for l in range(t));j+=2
  if j<len(s) and s[j]=='U':allowed.add((j,0,0));j+=1
 paths=[P for P in paths if set(P)<=allowed]
 cols=list(product(comps(a,len(V)),comps(b,len(U))));out={};entries=[]
 for col,(aa,bb) in enumerate(cols):
  for P in paths:
   pv=[V.index(e) for e in P if e in V];pu=[U.index(e) for e in P if e in U]
   if any(aa[i]==0 for i in pv):continue
   av=list(aa);bu=list(bb)
   for i in pv:av[i]-=1
   for i in pu:bu[i]+=1
   key=tuple(av),tuple(bu)
   if key not in out:out[key]=len(out)
   entries.append((out[key],col))
 A=[[0]*len(cols) for _ in out]
 for i,j in entries:A[i][j]+=1
 return rank(A,p)

def run():
 periodic_cases=[periodic(*z) for z in [(2,'VU',2,2,2,2),(2,'VUVU',1,2,2,2),(2,'VUU',1,3,3,0),(3,'VU',2,2,2,2),(2,'VUVU',2,2,2,2),(2,'VUU',2,2,2,2)]]
 booleans=[]
 for r in range(1,10):
  for d in range(1,r+1):
   rows=list(combinations(range(r),d-1));cols=list(combinations(range(r),d));A=[[int(set(x)<set(y)) for y in cols] for x in rows]
   assert rank(A,2)==comb(r-1,d-1)
  booleans.append(r)
 weighted_checks=0;x=Fraction(1,7);y=Fraction(1,5)
 for t in range(1,4):
  for h in product(range(4),repeat=t):
   levels,ranks=local_sector(h,2);H=sum(h)
   W=sum(len(b)*x**(H-e)*y**e for e,b in levels.items());R=sum(r*x**(H-e)*y**e for e,r in ranks.items())
   assert 4*R<=3*W;weighted_checks+=1
 # q=4 cannot be replaced by q=2 on sectors permitting occupation 2.
 _,rr=local_sector((2,),2);assert sum(rr.values())==2
 excursion=[]
 for w,s,t,a,b in [(2,'VU',2,2,1),(2,'VUVU',2,2,1),(2,'VUVUU',2,2,0)]:
  for p in [2,3,5]:
   exact=excursion_actual(w,s,t,a,b,p);formula=excursion_formula(w,s,t,a,b,p);assert exact==formula
   excursion.append({'width':w,'schedule':s,'t':t,'a':a,'b':b,'prime':p,'rank':exact})
 return {'status':'PASS','periodic_minors':periodic_cases,'boolean_levels_checked':sum(range(1,10)),'weighted_nilpotent_sectors':weighted_checks,'full_excursion_rank_comparisons':excursion,'scope':'Exact finite diagnostics only; not universal proof, formal certification or substantiality review.'}
if __name__=='__main__':
 import json;print(json.dumps(run(),indent=2))
