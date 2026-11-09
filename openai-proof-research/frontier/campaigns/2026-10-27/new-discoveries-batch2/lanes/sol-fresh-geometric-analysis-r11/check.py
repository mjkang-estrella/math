#!/usr/bin/env python3
"""Exact bounded route diagnostics, NOT a proof of Tao's conjecture."""
import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(20,20))
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
# None is -infinity. Negated endpoints in axiom (i) are +infinity.
def nc(pairs):
 total=0
 for bits in product((0,1),repeat=len(pairs)):
  vals=[pairs[i][bits[i]] for i in range(len(pairs))]
  infinities=[v for v in vals if isinstance(v,str)]
  assert not ('-' in infinities and '+' in infinities)
  s=(-1 if '-' in infinities else 1) if infinities else sum(vals)
  if not s:return False
  if s>0:total+=(-1)**sum(bits)
 return total==0

def failures(rows):
 out=[]
 for i,r in enumerate(rows):
  assert len(r)%2==1 and len(set(r))==len(r)
  e=['-',*r,'-']
  for p in range(len(r)+1):
   for q in range(p+2,len(r)+1,2):
    neg=tuple('+' if isinstance(v,str) else -v for v in e[q:q+2])
    if not nc((e[p:p+2],neg)):out.append(['i',i,p,q])
 for ps in product(*(range(len(r)+1) for r in rows)):
  if len({p%2 for p in ps})>1:continue
  pairs=[['-',*r,'-'][p:p+2] for r,p in zip(rows,ps)]
  if not nc(pairs):out.append(['ii',*ps])
 return out

def alt(rows):return sum(sum((-1)**j*v for j,v in enumerate(r)) for r in rows)
# Tao's perturbative family, Section 7: use integer scale epsilon=1.
rows=[[0,100,200],[0,20,40],[-1,-19,-41,-139,-121,-99,-201,-219,-241]]
assert not failures(rows)
assert alt(rows)==-9
out={'status':'exact diagnostics only','rows':rows,'alternating_sum':alt(rows),'deletions':[]}
for i,r in enumerate(rows):
 for j in range(len(r)-1):
  reduced=[a[:] for a in rows];reduced[i]=r[:j]+r[j+2:]
  bad=failures(reduced)
  delta=(-1)**j*(r[j]-r[j+1])
  out['deletions'].append(dict(row=i,j=j,removed_contribution=delta,preserves_axioms=not bad,first_failure=bad[:1],reduced_sum=alt(reduced)))
# Quantify potential greedy induction obstruction, no broad search.
out['admissible_upper_bound_deletions']=[d for d in out['deletions'] if d['preserves_axioms'] and d['removed_contribution']<=0]
assert len(out['deletions'])==12
assert not out['admissible_upper_bound_deletions']
assert sum(d['preserves_axioms'] for d in out['deletions'])==4
# Exact area/shear identities for arbitrary polygonal edges, incl horizontal winding.
def integral_y_dx(vertices):return sum((a[1]+b[1])*(b[0]-a[0])/2 for a,b in zip(vertices,vertices[1:]))
verts=[(F(0),F(2)),(F(1,3),F(5)),(F(2,3),F(-1)),(F(1),F(2))]
I=integral_y_dx(verts)
for sign,shear in [(1,1),(1,-1),(-1,0)]:
 transformed=[(x+shear*y,sign*y) for x,y in verts]
 assert integral_y_dx(transformed)==sign*I
out['shear_checks']=3
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
