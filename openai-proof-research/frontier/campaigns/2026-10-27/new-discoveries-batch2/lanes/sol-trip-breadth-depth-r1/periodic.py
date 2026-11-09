import itertools,json,runpy
from pathlib import Path
L=Path(__file__).resolve().parent;d=runpy.run_path(str(L/'checks.py'))
def compose(a,b):return [''.join(a[int(c)-1] for c in w) for w in b]
def double(j,k):return ['1'*(j+1)+'3','2'*(k+1)+'1'*j+'3','2'*k+'1'*j+'3']
def closure(s,N):
 F=set('123');rounds=0
 while True:
  H=set(F)
  for w in F:
   z=''.join(s[int(c)-1] for c in w)
   for n in range(1,min(N,len(z))+1):H.update(z[i:i+n] for i in range(len(z)-n+1))
  rounds+=1
  if H==F:return F,rounds
  F=H
  assert rounds<100
out=[]
for params in itertools.product(range(2),repeat=4):
 j,k,h,l=params;s=compose(double(j,k),double(h,l));F,r=closure(s,14)
 profiles=[]
 for w in sorted(F,key=lambda w:(len(w),w)):
  if len(w)>12:continue
  E={(int(a),int(b)) for a in '123' for b in '123' if a+w+b in F}
  if len({a for a,b in E})<3 or len({b for a,b in E})<3:continue
  z=[]
  for a in [(1,2,2),(0,2,3)]:
   for b in [(1,2,2),(0,2,1)]:
    G=d['image'](E,a,b);z.append(d['mult'](G) if len({x for x,y in G})>1 and len({y for x,y in G})>1 else 0)
  profiles.append(dict(word=w,E=sorted(E),m=d['mult'](E),positive_parameter_descendant_m=z))
 p=[sum(len(w)==n for w in F) for n in range(1,15)]
 assert all(v<=3*(i+1) for i,v in enumerate(p))
 out.append(dict(parameters=params,substitution=s,closure_rounds=r,p=p,graphs=profiles))
(L/'periodic.json').write_text(json.dumps(out,indent=2));print('exact stationary closures',len(out),'3x3 graphs',sum(len(x['graphs']) for x in out))
