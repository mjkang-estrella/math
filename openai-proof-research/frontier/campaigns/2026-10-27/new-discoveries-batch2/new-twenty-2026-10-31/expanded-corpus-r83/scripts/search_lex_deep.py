import itertools,math,json,time
from fractions import Fraction as F
from pathlib import Path
D=Path(__file__).resolve().parents[1];start=time.monotonic();count=0;bad=[];stats={}
def mons(d):return [(a,b,d-a-b) for a in range(d,-1,-1) for b in range(d-a,-1,-1)]
def gens(I):return [m for m in I if not any(tuple(m[j]-(j==k) for j in range(3)) in I for k in range(3) if m[k])]
def bs(gs):
 b={}
 for m in gs:
  d=sum(m);v=max(k for k in range(3) if m[k]);
  for i in range(v+1):b[i,d+i]=b.get((i,d+i),F(0))+math.comb(v,i)
 out=[]
 while b:
  p=max(i for i,d in b);ds=tuple(min(d for i,d in b if i==j) for j in range(p+1));pure=[F(1,math.prod(abs(ds[k]-ds[j]) for k in range(p+1) if k!=j)) for j in range(p+1)];c=min(b[j,ds[j]]/pure[j] for j in range(p+1));out.append((ds,c))
  for j in range(p+1):
   b[j,ds[j]]-=c*pure[j]
   if b[j,ds[j]]==0:del b[j,ds[j]]
 return [(ds,str(c)) for ds,c in out if len(ds)<3]
def run(I,previous,d,limit):
 global count
 if count>=300000 or time.monotonic()-start>105:return
 ms=mons(d);forced=0
 for k,m in enumerate(ms):
  if any(tuple(m[j]-(j==q) for j in range(3)) in previous for q in range(3) if m[q]):forced=k+1
 for cut in range(forced,len(ms)+1):
  current=set(ms[:cut]);J=I|current
  if cut==len(ms):
   gs=gens(J);a=bs(gs);h=gens({m for m in J if m[0]==0}|{(1,0,0)});b=bs(h);count+=1;stats[d]=stats.get(d,0)+1
   if a!=b:bad.append({'generators':gs,'L_suffix':a,'Lx_suffix':b})
  elif d<limit:run(J,current,d+1,limit)
run(set(),set(),1,11)
o={'count':count,'max_generator_degree':11,'by_terminal_degree':stats,'bad':bad[:10],'seconds':time.monotonic()-start,'complete':count<300000 and time.monotonic()-start<=105,'method':'all lex initial segments per degree with upward closure, terminal ideal includes whole degree; exact Eliahou-Kervaire and greedy pure rational decomposition'}
(D/'outputs/lex-deep-search.json').write_text(json.dumps(o,indent=2));print(json.dumps(o))
