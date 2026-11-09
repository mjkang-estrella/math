import numpy as np,itertools,json,math,random
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def s2(A):
 q=A+np.diag(A.sum(axis=0));return float(np.linalg.eigvalsh(q)[-2:].sum())
def cand(n,c):
 A=np.zeros((n,n));A[0,1:]=1;A[1:,0]=1
 for j in range(2,c+2):A[1,j]=A[j,1]=1
 return A
def connected(A):
 seen={0}
 while True:
  z=seen|{int(j) for i in seen for j in np.nonzero(A[i])[0]}
  if z==seen:return len(seen)==len(A)
  seen=z
out=[];random.seed(63)
for n in range(4,8):
 pairs=list(itertools.combinations(range(n),2)); targets={c:s2(cand(n,c)) for c in range(1,n-1)};best={c:(-1,None) for c in targets};counts={c:0 for c in targets}
 masks=range(1<<len(pairs)) if n<=6 else [random.getrandbits(len(pairs)) for _ in range(15000)]
 for mask in masks:
  c=mask.bit_count()-n+1
  if c not in targets:continue
  A=np.zeros((n,n));ed=[]
  for k,(i,j) in enumerate(pairs):
   if mask>>k&1:A[i,j]=A[j,i]=1;ed.append([i,j])
  if not connected(A):continue
  counts[c]+=1;t=s2(A)
  if t>best[c][0]:best[c]=(t,ed)
 out.append(dict(n=n,mode='exhaustive labeled' if n<=6 else '15000 seeded random masks',counts=counts,targets=targets,best=best,violations=[c for c in targets if best[c][0]>targets[c]+1e-8]))
(D/'outputs/spectral-diagnostics.json').write_text(json.dumps(out,indent=2)+'\n')
# Stars from the primary join formula, counts exactly in integers.
def stars(n,l,i,t):
 def b(x):return math.comb(x,t) if x>=t else 0
 z=(i+l)*b(n-1)+i*b(i+l)+(n-2*i-l)*b(n-i-1)
 return z//2 if t==1 else z
bad=[]; checked=0
for n in range(6,251):
 for l in [-1,0,1,2,3,4,5,10]:
  if l>n-5:continue
  i=(n-l-1)//2
  for t in range(1,(n+l+2)//2):
   if 2*t>=n+l+1:continue
   a=stars(n,l,i,t);b=stars(n,l,1,t);checked+=1
   if a>=b:bad.append(dict(n=n,l=l,t=t,a=str(a),b=str(b)))
(D/'outputs/star-diagnostics.json').write_text(json.dumps(dict(checked=checked,non_strict_or_reversed=bad[:150],total_failures=len(bad)),indent=2)+'\n')
print('spectral violations',[(x['n'],x['violations']) for x in out]);print('star comparisons',checked,'failures',len(bad),'first',bad[:6])
