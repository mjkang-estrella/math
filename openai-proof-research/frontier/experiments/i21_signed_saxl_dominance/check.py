"""Exact constructed-map diagnostics. No floating point or infinite extrapolation."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import importlib.util,json,math
from fractions import Fraction as Q
from itertools import permutations,product
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i21_signed_saxl_dominance';E=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('i19_frozen',S/'inputs/frontier/experiments/i19_fresh_structural_discovery/check.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
def parity(g):return (-1)**sum(g[i]>g[j] for i in range(len(g)) for j in range(i+1,len(g)))
def inv(g):return tuple(g.index(i) for i in range(len(g)))
def comp(g,h):return tuple(g[h[i]] for i in range(len(g)))
def act_word(g,w):r=[0]*len(w);[r.__setitem__(g[i],w[i]) for i in range(len(w))];return tuple(r)
def act(g,v):return {act_word(g,w):c for w,c in v.items()}
def dot(a,b):return sum(v*b.get(k,0) for k,v in a.items())
def add(a,b,k=1):
 c=a.copy()
 for x,v in b.items():c[x]=c.get(x,0)+k*v
 return {x:v for x,v in c.items() if v}
def ctype(g):
 unseen=set(g);cy=[]
 while unseen:
  a=next(iter(unseen));i=a;k=0
  while i in unseen:unseen.remove(i);i=g[i];k+=1
  cy.append(k)
 return tuple(sorted(cy,reverse=True))
def rank(A):
 A=[list(r) for r in A if any(r)];p=0
 if not A:return 0
 for j in range(len(A[0])):
  q=next((q for q in range(p,len(A)) if A[q][j]),None)
  if q is None:continue
  A[p],A[q]=A[q],A[p];a=A[p][j]
  for i in range(p+1,len(A)):
   b=A[i][j]
   if b:
    d=math.gcd(a,b);aa=a//d;bb=b//d
    A[i]=[aa*x-bb*y for x,y in zip(A[i],A[p])]
    d=math.gcd(*A[i])
    if d>1:A[i]=[x//d for x in A[i]]
  p+=1
  if p==len(A):break
 return p
def mm(A,B):return [[sum(x*y for x,y in zip(a,b)) for b in zip(*B)] for a in A]
def dominance_case(m):
 B=tuple((i,j) for i in range(1,m+1) for j in range(1,m+2-i));n=len(B)
 v=base.layer(B,'row');c=base.layer(B,'col');idg=tuple(range(n));G=list(permutations(range(n)))
 row=tuple(i for i,j in B);H=[g for g in G if act_word(g,row)==row]
 u={}
 for h in H:u=add(u,act(h,c))
 vv=dot(v,v);uu=dot(u,u);r=Q(uu,vv)
 av={};au={};vu={};uv={}
 for g in G:
  gv=act(g,v);gu=act(g,u)
  av[g]=dot(v,gv);au[g]=dot(u,gu);vu[g]=dot(v,gu);uv[g]=dot(u,gv)
  assert au[g]==r*parity(g)*av[g]
 sig=next(s for s in (1,-1) if all(uv[g]==s*parity(g)*vu[g] for g in G))
 kappa=sig*r
 reps={}
 for g in G:reps.setdefault(act_word(g,row),g)
 words=list(reps);gs=list(reps.values());ix={w:i for i,w in enumerate(words)};d=len(words)
 assert d==math.factorial(n)//len(H)
 grams={};zgram=[]
 for g in gs:
  zi=[]
  for h in gs:zi.append(av[comp(inv(g),h)]**2)
  zgram.append(zi)
 assert rank(zgram)==d
 for eps in (1,-1):
  D=[]
  for g in gs:
   a=[]
   for h in gs:
    q=comp(inv(g),h)
    a.append(parity(g)*parity(h)*2*(av[q]*au[q]+eps*vu[q]*uv[q]))
   D.append(a)
  grams[eps]=D
 out=[];actual=base.split(tuple(range(m,0,-1)))
 for lam in base.parts(n):
  P=[[0]*d for _ in range(d)]
  for g in G:
   z=base.chi(lam,ctype(g))*parity(g)
   if z:
    for j,w in enumerate(words):P[ix[act_word(g,w)]][j]+=z
  dim=base.chi(lam,(1,)*n);rr=[rank(mm(grams[eps],P)) for eps in (1,-1)]
  assert all(x%dim==0 for x in rr)
  mult=[x//dim for x in rr];assert all(a<=b for a,b in zip(mult,actual[lam]))
  out.append(dict(partition=lam,dimension=dim,map_ranks=rr,map_multiplicities=mult,full_square=actual[lam]))
 assert [sum(x['map_ranks'][i] for x in out) for i in (0,1)]==[rank(grams[e]) for e in (1,-1)]
 corr=[]
 for mu in base.parts(n):
  gg=[g for g in G if ctype(g)==mu]
  corr.append(dict(cycle_type=mu,class_size=len(gg),plus=sum(2*(av[g]*au[g]+vu[g]*uv[g]) for g in gg),minus=sum(2*(av[g]*au[g]-vu[g]*uv[g]) for g in gg)))
 return dict(class_correlations=corr,m=m,n=n,group_order=len(G),cosets=d,v_norm_squared=vv,u_norm_squared=uu,kappa=str(kappa),signed_intertwiner_gram_checks=len(G)*2,repeated_row_injection_rank=d,map_total_ranks=[rank(grams[e]) for e in (1,-1)],rows=out)
def wider_projections():
 ans=[]
 for m,s in [(4,3),(4,4)]:
  h=m-s;B=tuple((i,j) for i in range(1,m+1) for j in range(1,m+2-i));D=tuple(b for b in B if sum(b)<=h+1);A=tuple(b for b in B if b not in D)
  R=base.layer(B,'row');C=base.layer(B,'col');rh,ch=base.layer(D,'row'),base.layer(D,'col');ra,ca=base.layer(A,'row'),base.layer(A,'col')
  expected={}
  for (a,aa),(b,bb),(c,cc),(d,dd) in product(rh.items(),ch.items(),ra.items(),ca.items()):
   x=dict(zip(D,(v+s for v in a)));x.update(zip(A,c));y=dict(zip(D,(v+s for v in b)));y.update(zip(A,d));expected[tuple(x[v] for v in B),tuple(y[v] for v in B)]=aa*bb*cc*dd
  got={(a,b):aa*bb for a,aa in R.items() for b,bb in C.items() if all((x>s)==(y>s) for x,y in zip(a,b))}
  assert got==expected
  ans.append(dict(m=m,s=s,input_words=len(R)*len(C),retained_words=len(got)))
 # Optimistic signed targets use the entire band square, without assuming U equals it.
 optimistic=[]
 for m in (4,5,6):
  p=tuple(range(m,m-3,-1));band=base.split(p);small=base.split(tuple(range(m-3,0,-1)))
  actual=base.split(tuple(range(m,0,-1))) if m<6 else None
  n=m*(m+1)//2
  targets=base.parts(n) if m==4 else [tuple([2]*(n//2)+[1]*(n%2))]
  for lam in targets:
   vals=[0,0];prec=[]
   for nu,v in small.items():
    for eta,u in band.items():
     c=base.lr(lam,nu,eta)
     if c:
      vals[0]+=c*(v[0]*u[0]+v[1]*u[1]);vals[1]+=c*(v[0]*u[1]+v[1]*u[0])
      prec.append(dict(nu=nu,eta=eta,lr=c,small=v,band=u))
   if actual is not None:assert all(a<=b for a,b in zip(vals,actual[lam]))
   if m>4 or any(b and not a for a,b in zip(vals,actual[lam])):
    optimistic.append(dict(m=m,target=lam,optimistic_multiplicities=vals,actual=actual[lam] if actual else 'not computed',precursors=prec))
 assert next(x for x in optimistic if x['target']==(5,5))['optimistic_multiplicities']==[3,0]
 return dict(projection_cases=ans,optimistic_s3=optimistic)

def joint_sectors():
 out=[]
 for m in range(2,6):
  n=m*(m+1)//2;rho=tuple(range(m,0,-1));a=base.split(rho);d=(m+1)//2;h=tuple(2*m-4*i+3 for i in range(1,d+1));sig=(-1)**((n-d)//2)
  for lam,ss in a.items():
   trans=tuple(sum(v>=j for v in lam) for j in range(1,lam[0]+1));tt=a[trans];g=sum(ss);t=ss[0]-ss[1];tp=tt[0]-tt[1];hh=base.chi(lam,h)
   b={}
   for f in (1,-1):
    for k in (1,-1):
     q=Q(g+f*t+k*sig*hh+f*k*tp,4);assert q>=0 and q.denominator==1;b[str((f,k))]=int(q)
   assert b['(1, 1)']+b['(1, -1)']==ss[0] and b['(-1, 1)']+b['(-1, -1)']==ss[1]
   out.append(dict(m=m,partition=lam,principal_hooks=h,sigma=sig,joint_multiplicities=b))
 z=next(x for x in out if x['m']==3 and x['partition']==(4,1,1));assert z['joint_multiplicities']=={'(1, 1)':0,'(1, -1)':1,'(-1, 1)':2,'(-1, -1)':1}
 return out

def make_certificate(r):
 d=r['dominance'][1];B=tuple((i,j) for i in range(1,4) for j in range(1,5-i));v=base.layer(B,'row');c=base.layer(B,'col');row=tuple(i for i,j in B)
 H=[g for g in permutations(range(6)) if act_word(g,row)==row];u={}
 for h in H:u=add(u,act(h,c))
 return dict(positions=B,row_vector=sorted(v.items()),column_vector=sorted(c.items()),u_vector=sorted(u.items()),row_subgroup=H,class_correlations=d['class_correlations'],hook_character=[base.chi((3,1,1,1),tuple(z['cycle_type'])) for z in d['class_correlations']],scaled_plus_correlations=[z['plus']//6480 for z in d['class_correlations']],scale=6480,projector_norm_squared=0)

def main():
 r=dict(dominance=[dominance_case(m) for m in (2,3)],wider=wider_projections(),joint_sectors=joint_sectors(),status='exact assertions passed; finite diagnostics only')
 return r
if __name__=='__main__':
 r=main();(E/'dominance-m3-certificate.json').write_text(json.dumps(make_certificate(r),indent=2)+'\n');(E/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
