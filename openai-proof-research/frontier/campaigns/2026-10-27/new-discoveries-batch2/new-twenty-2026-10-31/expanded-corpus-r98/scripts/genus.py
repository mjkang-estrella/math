import json
from collections import Counter
from pathlib import Path
D=Path(__file__).resolve().parents[1];out=[]
# Set partitions encoded by increasing cycles, gamma=(1 ... n); 2g=n+1-cycles(alpha)-cycles(alpha^-1 gamma).
for n in range(1,11):
 counts=Counter();blocks=[]
 def gen(i):
  if i==n:
   alpha=list(range(n))
   for b in blocks:
    for a,c in zip(b,b[1:]+b[:1]):alpha[a]=c
   inv=[0]*n
   for a,b in enumerate(alpha):inv[b]=a
   pi=[inv[(a+1)%n] for a in range(n)];seen=set();cy=0
   for a in range(n):
    if a not in seen:
     cy+=1;b=a
     while b not in seen:seen.add(b);b=pi[b]
   v=n+1-len(blocks)-cy;assert v>=0 and v%2==0;counts[v//2,len(blocks)]+=1;return
  for b in blocks:b.append(i);gen(i+1);b.pop()
  blocks.append([i]);gen(i+1);blocks.pop()
 gen(0);o=dict(n=n,total=sum(counts.values()),counts={f'{g},{k}':c for (g,k),c in sorted(counts.items())});out.append(o);print(json.dumps(o),flush=True)
(D/'outputs/genus.json').write_text(json.dumps(out,indent=2)+'\n')
