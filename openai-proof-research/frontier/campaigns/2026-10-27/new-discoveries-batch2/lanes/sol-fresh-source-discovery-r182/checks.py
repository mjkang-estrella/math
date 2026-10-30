"""Bounded exact finite-field diagnostics; no all-degree assertion."""
import json,sys
from pathlib import Path
def rem(a,b):
 while a.bit_length()>=b.bit_length():a^=b<<(a.bit_length()-b.bit_length())
 return a
def gcd(a,b):
 while b:a,b=b,rem(a,b)
 return a
def mul(a,b,f):
 c=0;m=f.bit_length()-1
 while b:
  if b&1:c^=a
  b>>=1;a<<=1
  if a>>m:a^=f
 return c
def irr(f):
 m=f.bit_length()-1;x=2
 for j in range(1,m+1):
  x=mul(x,x,f)
  if j<=m//2 and gcd(x^2,f)!=1:return False
 return x==2
rows=[];derivatives=0
for e in range(3,8):
 m=2*e;N=1<<m
 f=next(f for f in range(N+1,2*N,2) if irr(f))
 sq=[mul(x,x,f) for x in range(N)];four=[sq[sq[x]] for x in range(N)]
 def tr(x):
  t=0
  for _ in range(e):t^=x;x=four[x]
  return t
 T=[tr(x) for x in range(N)];assert all(four[t]==t for t in T)
 F=[sq[four[x]]^mul(x,four[x],f)^mul(x,T[x],f) for x in range(N)]
 vals={};collision=None
 for x,v in enumerate(F):
  if v in vals and collision is None:collision=[vals[v],x,v]
  vals[v]=x
 # Compare literal source Q6.2 polynomial with its Frobenius normal form at every x.
 for x in range(N):
  orbit=[x]
  for _ in range(e-1):orbit.append(four[orbit[-1]])
  sm=0
  for z in orbit[:-1]:sm^=z
  s2=orbit[e-2]^orbit[e-1]
  source=mul(sm,T[x],f)^mul(s2,sm,f)^sq[T[x]]
  assert source==F[orbit[e-2]]
 # Derivative formula controls, including all x for selected nonzero directions.
 for a in [1,2,3,N//2,N-1]:
  c=sq[four[a]]^mul(a,four[a],f)^mul(a,T[a],f)
  for x in range(N):
   lin=mul(a,four[x],f)^mul(four[a],x,f)^mul(x,T[a],f)^mul(a,T[x],f)
   assert F[x^a]^F[x]==lin^c;derivatives+=1
 artin={}
 for z in range(N):artin.setdefault(four[z]^z,[]).append(z)
 curve_count=0;curve_witness=None
 for a in range(1,N):
  if T[a]:continue
  for z in artin.get(mul(sq[a],a,f)^1,[]):
   x=mul(a,z,f)
   if T[x]:continue
   assert F[x]==F[x^a]
   curve_count+=1
   if curve_witness is None:curve_witness=dict(a=a,z=z,x=x)
 rows.append(dict(e=e,field_size=N,modulus_binary=f,modulus_irreducible=True,image_size=len(vals),permutation=len(vals)==N,first_collision=collision,source_identity_checks=N,zero_trace_curve_pairs=curve_count,curve_witness=curve_witness))
result=dict(status='PASS',scope='e=3..7 only; not universal classification',rows=rows,derivative_formula_checks=derivatives)
out=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('checks.json')
out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
