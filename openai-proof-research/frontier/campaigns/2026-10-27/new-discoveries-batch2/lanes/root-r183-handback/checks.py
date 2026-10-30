import json,itertools,math
from pathlib import Path
L=Path(__file__).resolve().parent
def star(r,ss):
 a=[math.comb(s,2) for s in ss];raw=[math.comb(s-1,2) for s in ss];b=[max(1,x) for x in raw]
 bridge=sum(math.prod(b[:i]+b[i+1:]) for i in range(len(ss)))
 if r==1:return math.prod(a)+bridge
 if r==2:return math.prod(a)-math.prod(raw)+math.prod(b)+bridge
 return math.comb(r-1,2)*math.prod(a)+(r-1)*math.prod(b)+bridge
def graph(r,ss):
 es=list(itertools.combinations(range(r),2));v=r
 for s in ss:
  es+=list(itertools.combinations(range(v,v+s),2))+[(0,v)];v+=s
 return v,es
def counts(n,es):
 # Maximal induced matchings = maximal cliques of edge compatibility graph.
 adj=[set() for _ in range(n)]
 for u,v in es:adj[u].add(v);adj[v].add(u)
 comp=[]
 for i,(u,v) in enumerate(es):
  comp.append(sum(1<<j for j,(x,y) in enumerate(es) if i!=j and not ({u,v}&{x,y}) and not ({x,y}&(adj[u]|adj[v]))))
 out={}
 def bk(p,x,k):
  if not p and not x:out[k]=out.get(k,0)+1;return
  both=p|x
  if both:
   piv=max((i for i in range(len(es)) if both>>i&1),key=lambda i:(p&comp[i]).bit_count())
   choices=p&~comp[piv]
  else:choices=p
  while choices:
   bit=choices&-choices;i=bit.bit_length()-1
   bk(p&comp[i],x&comp[i],k+1);p^=bit;x|=bit;choices^=bit
 bk((1<<len(es))-1,0,0)
 return out
def parts(n,lo=2):
 if n==0:yield ();return
 for s in range(lo,n+1):
  for tail in parts(n-s,s):yield(s,)+tail
def I(n):
 if n<=8:return math.comb(n,2)
 if n<=13:
  a=n//2;b=n-a;return math.comb(a,2)*math.comb(b,2)-(a-1)*(b-1)+1
 z=n%5
 if z==4:return 36*10**((n-9)//5)+(3*n+363 if n<=44 else 9*n+99)*6**((n-14)//5)//5
 if z==0:return 6*10**((n-5)//5)+(n+115 if n<=50 else 3*n+15)*6**((n-10)//5)//5
 if z==1:return 10**((n-1)//5)+(n+144)*6**((n-6)//5)//30 if n<=30 else 10**((n-1)//5)+(n-1)*6**((n-6)//5)//5
 if z==2:return 15*10**((n-7)//5)+(n+141)*6**((n-12)//5)//3 if n<=32 else 15*10**((n-7)//5)+(2*n-8)*6**((n-12)//5)
 return 225*10**((n-13)//5)+(5*n+690)*6**((n-13)//5)//9 if n<=33 else 225*10**((n-13)//5)+(10*n-70)*6**((n-13)//5)//3
def main():
 verified=0
 for n in range(3,15):
  for r in range(1,n-1):
   for ss in parts(n-r):
    if not ss:continue
    a,e=graph(r,ss);actual=sum(counts(a,e).values());assert actual==star(r,ss),(r,ss,actual,star(r,ss));verified+=1
 optim=[];tested=0
 for n in range(14,46):
  best=0;args=[]
  for r in range(1,n-1):
   for ss in parts(n-r):
    if not ss:continue
    v=star(r,ss);tested+=1
    if v>best:best=v;args=[(r,ss)]
    elif v==best:args.append((r,ss))
  assert best==I(n),(n,best,I(n))
  optim.append(dict(n=n,maximum=best,optimizers=args))
 # Exact source obstruction to unrestricted cloning: C5 -> adjacent twins.
 cycle=[(i,(i+1)%5) for i in range(5)]
 clone=[e for e in cycle if 0 not in e]+[(0,1),(0,2)]
 assert sum(counts(5,cycle).values())==5 and sum(counts(5,clone).values())==4
 split=0
 for s in range(10,1001):
  assert 10*(s-5)*(s-6)-s*(s-1)==9*s*s-109*s+300
  assert 6*(s-6)*(s-7)-(s-1)*(s-2)==5*(s-5)*(s-10)
  assert math.comb(5,2)*math.comb(s-5,2)>math.comb(s,2)
  assert math.comb(4,2)*math.comb(s-6,2)>=math.comb(s-1,2);split+=1
 return dict(star_formula_controls=verified,star_optimization_cases=tested,range=[14,45],optimizers=optim,cloning_obstruction=[5,4],split_identity_controls=split,scope='Restricted clique-star diagnostic only; no universal extremal reduction or equality classification proved.')
if __name__=='__main__':(L/'checks.json').write_text(json.dumps(main(),indent=2)+'\n')
