"""Bounded exact formal-trace calculation; NOT a CE or minimality certificate."""
from itertools import permutations, combinations
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import json
OUT=Path(__file__).parent

def cyc(w): return min(w[i:]+w[:i] for i in range(len(w)))
def F(bs):
 p=Counter()
 for s in permutations(range(4)):
  seen=set(); cs=[]
  for i in range(4):
   if i in seen: continue
   c=[];j=i
   while j not in seen:
    seen.add(j);c+=bs[j];j=s[j]
   cs.append(cyc(tuple(c)))
  p[tuple(sorted(cs))]+=(-1)**(4-len(cs))
 return {k:Q(v) for k,v in p.items() if v}
def add(a,b,c):
 for k,v in b.items():
  a[k]=a.get(k,Q(0))+c*v
  if not a[k]: del a[k]
words=sorted(set(permutations((1,1,1,2,2,3,3))))
cols=set()
for w in words:
 for cuts in combinations(range(1,7),3):
  t=(0,)+cuts+(7,); cols.add(tuple(sorted(w[t[i]:t[i+1]] for i in range(4))))
cols=sorted(cols);basis={};kernels=[]
for bs in cols:
 p=F(bs);top={k:v for k,v in p.items() if len(k)==1};proof={bs:Q(1)}
 while top:
  lead=min(top)
  if lead not in basis:
   c=top[lead];basis[lead]=({k:v/c for k,v in top.items()},{k:v/c for k,v in p.items()},{k:v/c for k,v in proof.items()});break
  a,b,d=basis[lead];c=top[lead];add(top,a,-c);add(p,b,-c);add(proof,d,-c)
 else:
  if p:kernels.append((p,proof))
# First tuple as in Theorem4.1: verify exact full-trace contribution.
target=F(((1,1,1),(2,2),(3,),(3,)))
q,cert=min(kernels,key=lambda z:(len(z[0]),len(z[1])))
# Exact re-expansion of the saved dependence, separate from rank computation.
check={}
for bs,c in cert.items():add(check,F(bs),c)
assert check==q and all(len(m)>1 for m in q)
def term(p):return [{'traces':[''.join(map(str,w)) for w in m],'coefficient':str(c)} for m,c in sorted(p.items())]
r={'scope':'formal trace polynomial ring modulo cyclic word equivalence only; not reduced to Lemma3.2 generators', 'multidegree':[3,2,2], 'tuple_columns':len(cols),'single_trace_rows':len({k for bs in cols for k in F(bs) if len(k)==1}), 'exact_single_trace_rank':len(basis),'nonzero_decomposable_kernel_outputs':len(kernels),'target_top':term({k:v for k,v in target.items() if len(k)==1}),'small_decomposable_identity':term(q),'identity_certificate':[{'blocks':[''.join(map(str,w)) for w in bs],'coefficient':str(c)} for bs,c in cert.items()],'reexpanded_exactly':True,'limitation':'Kernel outputs can be consequences of lower-degree identities and can reduce to zero in CE. No admissible degree7 multilinear reduction or exceptional parameter is certified.'}
(OUT/'trace-degree7-diagnostics.json').write_text(json.dumps(r,indent=2));print({k:v for k,v in r.items() if k not in ['small_decomposable_identity','identity_certificate']})
# Continue modulo *all* products of lower-degree fundamental identities in this
# multidegree, rather than mistaking a nonzero formal polynomial for a relation
# between the chosen minimal generators.
import signal
signal.alarm(50)
from functools import lru_cache
TARGET=(3,2,2)
def deg(w):return tuple(w.count(i) for i in (1,2,3))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
@lru_cache(None)
def necklaces(d):
 if any(x<0 for x in d) or not sum(d):return ()
 return tuple(sorted({cyc(w) for w in set(permutations(tuple(i for i,n in zip((1,2,3),d) for _ in range(n))))}))
all_ds=[(a,b,c) for a in range(4) for b in range(3) for c in range(3)]
@lru_cache(None)
def trace_monomials(d,lo=()):
 if not sum(d):return ((),)
 out=[]
 for dd in all_ds:
  if not sum(dd) or any(x>y for x,y in zip(dd,d)):continue
  for w in necklaces(dd):
   if w<lo:continue
   for rest in trace_monomials(sub(d,dd),w):out.append((w,)+rest)
 return tuple(out)
low_basis={};low_cols=0;lower_polynomials=[]
for dd in all_ds:
 if not 4<=sum(dd)<=6:continue
 ws=set(permutations(tuple(i for i,n in zip((1,2,3),dd) for _ in range(n))))
 tuples=set()
 for w in ws:
  for cuts in combinations(range(1,len(w)),3):
   t=(0,)+cuts+(len(w),);tuples.add(tuple(sorted(w[t[i]:t[i+1]] for i in range(4))))
 for bs in sorted(tuples):
  f=F(bs)
  for m in trace_monomials(sub(TARGET,dd)):
   low_cols+=1;p={tuple(sorted(k+m)):v for k,v in f.items()};lower_polynomials.append(dict(p))
   while p:
    lead=min(p,key=lambda x:(-max(map(len,x)),x))
    if lead not in low_basis:
     c=p[lead];low_basis[lead]={k:v/c for k,v in p.items()};break
    add(p,low_basis[lead],-p[lead])
def low_reduce(p):
 p=dict(p);out={}
 while p:
  lead=min(p,key=lambda x:(-max(map(len,x)),x))
  if lead in low_basis:add(p,low_basis[lead],-p[lead])
  else:out[lead]=p.pop(lead)
 return out
nonzero=[]
for p,cert in kernels:
 rr=low_reduce(p)
 if rr: nonzero.append((rr,p,cert))
r['lower_degree_product_columns']=low_cols;r['lower_degree_product_rank']=len(low_basis);r['kernel_outputs_nonzero_mod_lower']=len(nonzero)
if nonzero:
 rr,p,cert=min(nonzero,key=lambda z:len(z[0]));r['nonzero_mod_lower_example']=term(rr);r['nonzero_mod_lower_certificate']=[{'blocks':[''.join(map(str,w)) for w in bs],'coefficient':str(c)} for bs,c in cert.items()]
# Rank of these relation classes in the lower-degree quotient.
rb={}
for p,_,_ in nonzero:
 p=dict(p)
 while p:
  lead=min(p)
  if lead not in rb:
   c=p[lead];rb[lead]={k:v/c for k,v in p.items()};break
  add(p,rb[lead],-p[lead])
r['new_decomposable_relation_class_rank']=len(rb)
(OUT/'trace-degree7-diagnostics.json').write_text(json.dumps(r,indent=2));print({k:r[k] for k in ['lower_degree_product_columns','lower_degree_product_rank','kernel_outputs_nonzero_mod_lower','new_decomposable_relation_class_rank']})
# Polarize a decomposable identity and apply the exact three canonical full-trace
# substitutions arising from the first displayed tuple. No random evaluations.
rr,q,cert=min(nonzero,key=lambda z:len(z[0]))
polar={}
for mon,c in q.items():
 positions={a:[] for a in (1,2,3)}
 for j,w in enumerate(mon):
  for h,a in enumerate(w):positions[a].append((j,h))
 for a in permutations((1,2,3)):
  for b in permutations((4,5)):
   for cc in permutations((6,7)):
    words=[list(w) for w in mon]
    for letter,labels in zip((1,2,3),(a,b,cc)):
     for (j,h),v in zip(positions[letter],labels):words[j][h]=v
    key=tuple(sorted(cyc(tuple(w)) for w in words));polar[key]=polar.get(key,Q(0))+c
polar={k:v for k,v in polar.items() if v}
delta={}
for pattern in [(1,1,1,2,2,3,3),(1,1,1,3,2,2,3),(1,1,1,3,3,2,2)]:
 for mon,c in polar.items():
  key=tuple(sorted(cyc(tuple(pattern[a-1] for a in w)) for w in mon));delta[key]=delta.get(key,Q(0))-2*c
delta={k:v for k,v in delta.items() if v};dr=low_reduce(delta)
lead=min(rr);ratio=dr.get(lead,Q(0))/rr[lead];assert dr=={k:v*ratio for k,v in rr.items() if v*ratio}
r['polarized_deformation']={'polarized_terms':len(polar),'degree7_formal_delta_terms':len(delta),'delta_mod_lower_multiple':str(ratio),'exact_proportionality_verified':True,'note':'This test concerns one nonzero relation-class deformation, not all multilinear degree7 identities.'}
(OUT/'trace-degree7-diagnostics.json').write_text(json.dumps(r,indent=2));print(r['polarized_deformation'])

# Save exact polynomials separately from the exploratory rank report.
packet={'q':term(q),'q_fundamental_certificate':[{'blocks':[''.join(map(str,w)) for w in bs],'coefficient':str(c)} for bs,c in cert.items()],'polarized_q':term(polar),'delta':term(delta),'lower_identity_products':[term(p) for p in lower_polynomials],'claim':'delta + 72*q belongs to the span of lower_identity_products; q does not'}
(OUT/'trace-exact-polynomials.json').write_text(json.dumps(packet,indent=2))
