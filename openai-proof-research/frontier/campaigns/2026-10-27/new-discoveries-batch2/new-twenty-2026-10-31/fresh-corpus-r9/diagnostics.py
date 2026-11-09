from pathlib import Path
import json,itertools,time
p=Path(__file__).resolve().parent
out=[]
for n in range(1,9):
 c=(3*n*n+6*n+4)//4 if n%2==0 else (3*n*n+6*n+3)//4
 checked=0; witness=None
 for a,b,d in itertools.combinations(range(1,c),3):
  checked+=1; good=True
  for x in range(-2*n,2*n+1):
   for y in range(-(2*n-abs(x)),2*n-abs(x)+1):
    znum=-x*a-y*b
    if znum%d==0 and (x or y or znum) and abs(x)+abs(y)+abs(znum//d)<=2*n:
     good=False;break
   if not good:break
  if good:witness=[a,b,d];break
 out.append(dict(n=n,c_n=c,distinct_increasing_triples_checked=checked,counterexample=witness))
(p/'lissajous-diagnostic.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
