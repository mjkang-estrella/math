"""Bounded finite evaluation certificates for no CE relations in the needed box below degree 7."""
from pathlib import Path
from itertools import product
from fractions import Fraction as Q
import json,random,signal
signal.alarm(90)
p=Path(__file__).parent;el=json.loads((p/'finite-elimination.json').read_text());expr=el['E_formulas']
expr.update({'36':'112212-221121','37':'113313-331131','38':'223323-332232','39':'112123+112132+113122-112213-112312-113212','40':'221213+221231+223211-221123-221321-223121','41':'332321+332312+331322-332231-332132-331232','42':'113132+113123+112133-113312-113213-112313','43':'223231+223213+221233-223312-223123-223132','44':'331312+331321+332111-331132-331231-332131','45':'112233+113232+121332+123123+131322-112323-113322-121233-122313-132132'})
# Correct literal t44 term z² y z x² = 332311, not a six-letter word with three x's.
expr['44']='331312+331321+332311-331132-331231-332131'
# Source: t44 = tr(z²xzxy)+tr(z²xzyx)+tr(z²yzx²)-tr(z²x²zy)-tr(z²xyzx)-tr(z²yxzx).
# tr(z²yzx²) = 332311; first two =331312,331321.
import re
E={};degrees={}
for k,s in expr.items():
 ts=[]
 for sign,c,w in re.findall(r'([+-]?)(?:(\d+)\*)?([123]+)',s):ts.append(((-1 if sign=='-' else 1)*int(c or 1),tuple(map(int,w))))
 d=tuple(ts[0][1].count(a) for a in (1,2,3));assert all(tuple(w.count(a) for a in (1,2,3))==d for _,w in ts),(k,ts)
 E[int(k)]=ts;degrees[int(k)]=d
def mm(A,B):return [[sum(A[i][k]*B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
def vals(mats):
 cache={():[[int(i==j) for j in range(3)] for i in range(3)]}
 def tr(w):
  if w not in cache:cache[w]=mm(matrix(w[:-1]),mats[w[-1]-1])
  return sum(cache[w][i][i] for i in range(3))
 def matrix(w):
  tr(w);return cache[w]
 return {i:sum(c*tr(w) for c,w in ts) for i,ts in E.items()}
def mons(d,lo=1):
 if not any(d):return [()]
 r=[]
 for i,dd in degrees.items():
  if i>=lo and all(x<=y for x,y in zip(dd,d)):
   r.extend((i,)+m for m in mons(tuple(y-x for x,y in zip(dd,d)),i))
 return r
rng=random.Random(321413);samples=[];values=[]
for _ in range(80):
 mats=[]
 for j in range(3):
  A=[[rng.randrange(-2,3) for k in range(3)] for i in range(3)];A[2][2]=-A[0][0]-A[1][1];mats.append(A)
 samples.append(mats);values.append(vals(mats))
records=[]
import sympy as sp
for d in product(range(7),repeat=3):
 if not 1<=sum(d)<=6:continue
 ms=mons(d)
 if not ms:continue
 piv={};sel=[];rows=[]
 for si,v in enumerate(values):
  row=[]
  for m in ms:
   a=1
   for i in m:a*=v[i]
   row.append(a)
  rr=list(map(Q,row))
  for i,b in sorted(piv.items()):
   a=rr[i]
   if a:rr=[x-a*y for x,y in zip(rr,b)]
  nz=next((i for i,x in enumerate(rr) if x),None)
  if nz is not None:
   a=rr[nz];piv[nz]=[x/a for x in rr];sel.append(si);rows.append(row)
  if len(sel)==len(ms):break
 assert len(sel)==len(ms),(d,len(sel),len(ms))
 mat=sp.Matrix(rows);inv=mat.inv();assert mat*inv==sp.eye(len(ms))
 records.append({'multidegree':d,'CE_monomials':ms,'sample_indices':sel,'evaluation_matrix':rows,'inverse':[[str(inv[i,j]) for j in range(len(ms))] for i in range(len(ms))]})
packet={'scope':'traceless E monomial independence for all nonempty multidegrees of total<=6; exact evaluation/inverse certificates, not Lean checked','E_formulas':expr,'samples':samples,'components':records,'max_dimension':max(len(r['CE_monomials']) for r in records)}
(p/'low-injectivity.json').write_text(json.dumps(packet,indent=2));print({'components':len(records),'max_dimension':packet['max_dimension'],'total_monomials':sum(len(r['CE_monomials']) for r in records),'status':'PASS exact inverses'})
