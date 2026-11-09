import itertools,math,json,pathlib,time
from fractions import Fraction
D=pathlib.Path(__file__).resolve().parents[1]
def rank(cols):
 basis={}
 for col in cols:
  v={j:Fraction(x) for j,x in enumerate(col) if x}
  while v:
   p=max(v)
   if p not in basis:
    d=v[p];basis[p]={j:x/d for j,x in v.items()};break
   d=v[p]
   for j,x in basis[p].items():
    v[j]=v.get(j,0)-d*x
    if v[j]==0:del v[j]
 return len(basis)
start=time.monotonic();out={'domain':'Three distinct projective roots normalized to 0,1,infinity; all partitions with 1<=c<=b<=a<=35 until time cap','tested':0,'last':None,'mismatches':[]}
for a in range(1,36):
 for b in range(1,a+1):
  for c in range(1,b+1):
   if time.monotonic()-start>100:break
   perms=list(set(itertools.permutations((a,b,c))));total=a+b+c
   criterion=False
   for mask in range(1,1<<len(perms)):
    S=[p for j,p in enumerate(perms) if mask>>j&1]
    if len(S)>=total-sum(min(p[i] for p in S) for i in range(3))+2:criterion=True;break
   cols=[]
   for u,v,w in perms:
    col=[0]*(u+v+1)
    for j in range(v+1):col[u+j]=math.comb(v,j)*(-1)**(v-j)
    cols.append(col)
   dep=rank(cols)<len(cols);out['tested']+=1;out['last']=[a,b,c]
   if criterion!=dep:out['mismatches'].append({'mu':[a,b,c],'criterion':criterion,'dependent':dep})
  if time.monotonic()-start>100:break
 if time.monotonic()-start>100:break
out['wall_seconds']=time.monotonic()-start;(D/'outputs/radical.json').write_text(json.dumps(out,indent=2));print(out)
