#!/usr/bin/env python3
"""Exact finite free-product checks only; not a proof of T296O."""
import json,sys,random
from fractions import Fraction as Q
from functools import lru_cache
from collections import Counter
from pathlib import Path
# Gaussian rationals, no floating point.
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def neg(a):return(-a[0],-a[1])
def mul(a,b):return(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
Z=(Q(0),Q(0));O=(Q(1),Q(0));roots=[O,(Q(0),Q(1)),(-Q(1),Q(0)),(Q(0),-Q(1))]
def fr(w):
 s=[]
 for a in w:
  if s and s[-1]==-a:s.pop()
  else:s.append(a)
 return tuple(s)
def norm(w):
 s=[]
 for typ,val in w:
  while s and s[-1][0]==typ:
   old=s.pop()[1];val=(old+val)%4 if typ=='d' else fr(old+val)
  if val:s.append((typ,val))
 return tuple(s)
def inv(w):return tuple((t,(-v)%4 if t=='d' else tuple(-a for a in reversed(v))) for t,v in reversed(w))
def g(k):return(('g',(k,)),)
u=(('d',1),);y=g(100)
laws=[(Q(1,4),)*4,(Q(3,4),0,Q(1,4),0),(Q(1,2),Q(1,3),Q(1,6),0),(Q(1,7),Q(2,7),Q(3,7),Q(1,7)),(1,0,0,0),(0,1,0,0)]
results=[];nchecks=0;negative={}
for weights in laws:
 moments=[]
 for k in range(4):
  a=Z
  for j,p in enumerate(weights):a=add(a,mul((Q(p),Q(0)),roots[(j*k)%4]))
  moments.append(a)
 @lru_cache(None)
 def tr(w):
  w=norm(w)
  if not w:return O
  if len(w)==1:return moments[w[0][1]] if w[0][0]=='d' else Z
  pos=[i for i,(t,v) in enumerate(w) if t=='d'];n=len(pos);answer=Z
  # Alternating centered syllables have trace zero. Solve for full raw word.
  for mask in range((1<<n)-1):
   keep={pos[j] for j in range(n) if mask>>j&1};coeff=O
   for i in pos:
    if i not in keep:coeff=mul(coeff,neg(moments[w[i][1]]))
   reduced=tuple(a for i,a in enumerate(w) if a[0]!='d' or i in keep)
   answer=add(answer,mul(coeff,tr(norm(reduced))))
  return neg(answer)
 beta=add(O,neg(mul(moments[1],moments[3])))
 for ell in range(1,7):
  response=Z
  for k in range(1,ell+1):
   for j in range(1,ell+1):
    p=g(k)+inv(g(j));q=g(k)+u+inv(g(j))
    for label,sign in [(p,1),(q,-1)]:
     forward=tr(norm(label+y+inv(label)+inv(y)))
     backward=tr(norm(label+inv(y)+inv(label)+inv(y)))
     response=add(response,mul((Q(sign),Q(0)),add(forward,neg(backward))))
     nchecks+=2
  assert response==mul((Q(ell),Q(0)),beta)
  nchecks+=1
 if weights==laws[2]:
  negative['replace_abs_trace_squared_by_trace_squared']=beta!=add(O,neg(mul(moments[1],moments[1])))
 if weights==laws[-1]:negative['omit_negative_conjugation_half']=beta!=O
 rng=random.Random(296)
 for _ in range(100):
  word=tuple(('d',rng.choice([1,2,3])) if rng.randrange(3)==0 else ('g',(rng.choice([-3,-2,-1,1,2,3]),)) for _ in range(8))
  degree=fr(tuple(a for t,v in word if t=='g' for a in v))
  if degree:assert tr(norm(word))==Z;nchecks+=1
 results.append({'weights':[str(Q(x)) for x in weights],'trace_u':[str(x) for x in moments[1]],'beta':[str(x) for x in beta]})
for ell in range(1,31):
 counts=Counter(fr((k,-j)) for k in range(1,ell+1) for j in range(1,ell+1))
 assert counts[()]==ell
 assert sum(x*x for x in counts.values())==2*ell*ell-ell
 assert all(x==1 for p,x in counts.items() if p)
 nchecks+=3
negative['treat_identity_label_as_single_occurrence']=(sum(x*x for x in counts.values()) != 1+ell*(ell-1))
assert all(negative.values())
record={'status':'PASS','exact_checks':nchecks,'spectral_laws':results,'negative_controls_detected':negative,'limits':'Finite free-product trace identities and group multiplicities only. No infinite-factor, Baire, norm-clipping, source compiler or theorem certification.'}
out=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('diagnostics-results.json')
out.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({'status':'PASS','exact_checks':nchecks,'negative_controls':len(negative)}))
