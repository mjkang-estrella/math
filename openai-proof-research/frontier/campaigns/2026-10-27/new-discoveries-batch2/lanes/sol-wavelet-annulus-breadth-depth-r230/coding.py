from fractions import Fraction as F
from pathlib import Path
import json
L=Path(__file__).resolve().parent
def intersect(A,B):
 A=sorted(A);B=sorted(B);i=j=0;out=[]
 while i<len(A) and j<len(B):
  a,b=A[i];c,d=B[j]
  if max(a,c)<min(b,d):out.append((max(a,c),min(b,d)))
  if b<d:i+=1
  else:j+=1
 return merge(out)
def merge(A):
 out=[]
 for a,b in sorted(A):
  if out and a<=out[-1][1]:out[-1]=(out[-1][0],max(b,out[-1][1]))
  else:out.append((a,b))
 return out
def step(S,b):
 original=S
 # Open cells only; finitely many endpoints are null. Missing edges impose no constraint.
 for lo,hi,c,d in [(F(1),F(3,2),F(-2),F(4)),(F(3,2),2-2*b,F(-4),F(8)),(F(1),2-2*b,F(-1,2),F(2)),(8*b,2-2*b,F(-1,4),F(2))]:
  if lo>=hi:continue
  pre=[((v-d)/c,(u-d)/c) for u,v in original]
  allowed=merge([(F(1),lo),(hi,F(2))]+intersect([(lo,hi)],pre))
  S=intersect(S,allowed)
 return S
results=[]
for b in [F(1,6),F(13,100),F(1,7),F(3,20),F(4,25),F(33,200),F(1,8)]:
 S=[(F(1),2-2*b)];rr=[]
 for n in range(45):
  rr.append({'n':n,'cells':len(S),'length':str(sum((v-u for u,v in S),F(0))),'intervals':[[str(u),str(v)] for u,v in S[:12]]})
  if not S:break
  S=step(S,b)
  if len(S)>12000:break
 results.append({'b':str(b),'iterations':rr})
 print(str(b),rr[-1],flush=True)
(L/'coding-checks.json').write_text(json.dumps(results,indent=2))
