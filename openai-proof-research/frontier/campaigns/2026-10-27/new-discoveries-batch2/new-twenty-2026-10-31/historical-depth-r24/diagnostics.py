import random,json,pathlib,resource,itertools
from fractions import Fraction as F
resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,768*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(55,55))
D=pathlib.Path(__file__).resolve().parent;rng=random.Random(2401)
def extensions(pred):
 n=len(pred)
 def rec(seq,used):
  if len(seq)==n:yield tuple(seq);return
  for v in range(n):
   if not (used>>v)&1 and pred[v]&used==pred[v]:yield from rec(seq+[v],used|(1<<v))
 yield from rec([],0)
def evaluate(pred,x):
 n=len(pred);count=s1=s2=sw=0
 for seq in extensions(pred):
  pos={v:i+1 for i,v in enumerate(seq)};p=pos[x];q=max([0]+[pos[v] for v in range(n) if pred[x]>>v&1]);r=min([n+1]+[pos[v] for v in range(n) if pred[v]>>x&1]);count+=1;s1+=p;s2+=p*p;sw+=r-q
 mean=F(s1,count);var=F(s2,count)-mean*mean;win=F(sw,count)
 # independent deletion/insertion weighted moments
 vs=[v for v in range(n) if v!=x];pr=[sum(1<<j for j,v in enumerate(vs) if pred[w]>>v&1) for w in vs];z=z1=z2=zw=0
 for seq in extensions(pr):
  pos={vs[v]:i+1 for i,v in enumerate(seq)};lo=max([0]+[pos[v] for v in vs if pred[x]>>v&1]);hi=min([n]+[pos[v] for v in vs if pred[v]>>x&1]);W=hi-lo
  z+=W;z1+=sum(range(lo+1,hi+1));z2+=sum(j*j for j in range(lo+1,hi+1));zw+=W*(W+1)
 assert (count,s1,s2,sw)==(z,z1,z2,zw)
 return dict(n=n,x=x,extensions=count,var=str(var),win=str(win),ratio=str(var/(n*win)),pred=pred)
rows=[]
for n in range(3,9):
 for trial in range(20):
  pred=[0]*n;p=rng.choice([.12,.25,.45,.7])
  for j in range(n):
   for i in range(j):
    if rng.random()<p:pred[j]|=(1<<i)|pred[i]
  rows.append(evaluate(pred,rng.randrange(n)))
best=max(rows,key=lambda x:F(x['ratio']));print('posets',len(rows),'max ratio',best);print('all deletion weighted moment identities verified')
family=[]
for m in range(2,6):
 for k in range(1,4):
  pred=[(1<<j)-1 if j<m else ((1<<j)-(1<<m)) for j in range(m+k)];x=m//2;z=evaluate(pred,x);r=x+1;n=m+k
  v=F(r*(m-r+1)*(n+1)*(n-m),(m+1)**2*(m+2));w=F(2*(n+1),m+1)
  assert z['var']==str(v) and z['win']==str(w);family.append(z)
print('two-chain exact formula checks',len(family))
# finite tests of local halfsum obstruction, not all-n proof
half=[]
for n in range(5,2002,4):
 m=(n-1)//2;rem=sum(pow(j,m,n**3) for j in range(1,n))%(n**3)
 if rem==0:half.append(n)
print('halfsum n=5..2001 mod4=1 zeros',half)
# direct collapsing symbols does not preserve determinism
trans=[('R','z','S'),('R','0','T'),('S','0','R'),('T','1','R')]
for a in ['z','0','1']:
 edges=[(s,t) for s,b,t in trans if a==b];assert len(set(s for s,t in edges))==len(edges)==len(set(t for s,t in edges))
collapsed=[(s,'0' if a=='z' else a,t) for s,a,t in trans];print('valid reversible period-2 graph code {z0,01}; relabel z->0 collision',collapsed[:2])
(D/'diagnostics.json').write_text(json.dumps(dict(posets=rows,two_chain=family,halfsum_zeros=half,capacity_collapse=collapsed),indent=2))
