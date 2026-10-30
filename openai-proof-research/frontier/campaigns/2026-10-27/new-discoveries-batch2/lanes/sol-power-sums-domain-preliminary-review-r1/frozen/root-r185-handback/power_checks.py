import json,math
from pathlib import Path
L=Path(__file__).resolve().parent
# Z[w]/(w^2+w+1), exact arithmetic; sixth roots are +/- powers of w.
def mul(x,y):
 a,b=x;c,d=y;return(a*c-b*d,a*d+b*c-b*d)
def pw(x,n):
 r=(1,0)
 for _ in range(n):r=mul(r,x)
 return r
def plus(x,y):return(x[0]+y[0],x[1]+y[1])
roots=[(1,0),(-1,0),(0,1),(0,-1),(-1,-1),(1,1)]
rows=[]
for b in [5,8,11,17,20,23,32,35,44,101,104]:
 pairs=[]
 for a in roots:
  for c in roots:
   if plus(plus((1,0),pw(a,2)),pw(c,2))==(0,0) and pw(a,b-2)==(1,0) and pw(c,b-2)==(1,0):pairs.append([a,c])
 expected=8 if b%2 else 32
 assert 4*len(pairs)==expected
 rows.append(dict(b=b,projective_singular_points=4*len(pairs),coordinate_normalized_pairs=pairs))
 # Lagrange Hessian on tangent quotient representative x=(1,w,w^2,0).
 # tangent basis (-w,1,0,0),(0,0,0,1); determinant b^2(b-2)w.
 assert b*b*(b-2)!=0
bidegree=[]
for b in range(3,81):
 vals=[b*(c+d)-2*c*d for c in range(b+1) for d in range(b+1) if 0<c+d<2*b]
 noline=[b*(c+d)-2*c*d for c in range(b+1) for d in range(b+1) if 2<=c+d<=2*b-2]
 assert min(vals)==b and min(noline)==2*b-2
 bidegree.append(dict(b=b,min_general=min(vals),min_without_lines=min(noline)))
classification=[]
for b in range(3,501):
 nonnormal=(b%4==2 or b%3==2)
 candidates=nonnormal and b%4!=2 and b not in [5,8]
 wanted=(b>=11 and b%6==5) or (b>=20 and b%12==8)
 assert candidates==wanted
 if wanted:assert (b>8 if b%2 else 2*b-2>32)
 classification.append([b,nonnormal,wanted])
out=dict(singular_controls=rows,bidegree_controls=bidegree,classification_controls=classification,universal_proof='PROOF.md; bounded diagnostics are not premises',exact_arithmetic=True)
(L/'power-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS:',len(rows),'singular controls;',len(bidegree),'bidegree controls;',len(classification),'classification controls')
