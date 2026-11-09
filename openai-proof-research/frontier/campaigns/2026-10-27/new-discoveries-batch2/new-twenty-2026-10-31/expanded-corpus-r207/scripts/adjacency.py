from pathlib import Path
import json,itertools,time
L=Path(__file__).resolve().parents[1];out={}
for m in range(1,9):
 D=[{}, {(1,1):1}];seq=[1,1]
 for n in range(2,61):
  R={}
  for a in range(n):
   b=n-1-a
   if a and b:
    if a>=m:continue
    aa={};bb={}
    for (f,l),v in D[a].items():
     if a+1-l<=m:aa[f]=aa.get(f,0)+v
    for (f,l),v in D[b].items():
     if n-f<=m:bb[l]=bb.get(l,0)+v
    for f,v in aa.items():
     for l,w in bb.items():R[f+b,l]=R.get((f+b,l),0)+v*w
   elif a==0:
    for (f,l),v in D[b].items():
     if n-f<=m:R[n,l]=R.get((n,l),0)+v
   else:
    for (f,l),v in D[a].items():
     if n-l<=m:R[f,n]=R.get((f,n),0)+v
  D.append(R);seq.append(sum(R.values()))
 # independent brute-force all permutations through n=7
 brute=[]
 for n in range(1,8):
  c=0
  for p in itertools.permutations(range(1,n+1)):
   if any(abs(p[i]-p[i+1])>m for i in range(n-1)):continue
   if any(p[i]<p[k]<p[j] for i in range(n) for j in range(i+1,n) for k in range(j+1,n)):continue
   c+=1
  assert c==seq[n],(m,n,c,seq[n]);brute.append(c)
 out[str(m)]={'counts_n0_to60':seq,'independent_all_permutations_n1_to7':brute};print(m,seq[:15],flush=True)
(L/'outputs/adjacency.json').write_text(json.dumps(out,indent=2))
