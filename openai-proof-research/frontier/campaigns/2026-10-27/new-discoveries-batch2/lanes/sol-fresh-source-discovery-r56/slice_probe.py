from check import neighbors,closure
import random,json
from pathlib import Path
rng=random.Random(56);out=[]
for m,n in [(3,5),(4,4)]:
 N=m*n;full=(1<<N)-1;nb=neighbors(m,n);ok=[closure(full^v,nb)==full for v in range(1<<N)];fail=None
 for t in range(10000):
  union=full if t<5000 else rng.randrange(full+1)
  inter=rng.randrange(full+1)&union;D=union^inter;d=D.bit_count()
  if d%2:continue
  c=[0]*(d+1);x=D
  while True:
   if ok[inter|x] and ok[inter|(D^x)]:c[x.bit_count()]+=1
   if not x:break
   x=(x-1)&D
  if d and c[d//2]<c[d//2-1]:fail={'inter':inter,'union':union,'D':D,'counts':c};break
 out.append({'m':m,'n':n,'draws':t+1,'central_failure':fail})
Path('slice-probe.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
