import pathlib,json,time,random,math,sys
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);seed=int(sys.argv[2]);rng=random.Random(seed)
base={14:[1,4,5,7,2,4,6,7,3,4,7,8,4,4],16:[1,8,5,4,2,8,6,4,3,8,7,4,4,8,8,8]}[n];cap=sum(base)-1
# For even cycles, replication is perfect. At threshold k, a bad subset
# is an independent set of the cycle edges whose endpoint weight sum >= k,
# restricted to vertices whose own weight < k. DP gives its maximum size.
def deficiencies(w):
 out=[]
 for k in range(2,n+1):
  best=-1
  for first in [0,1]:
   if first and w[0]>=k:continue
   a,b=(0,-999) if first==0 else (-999,1)
   for i in range(1,n):
    nb=max(a,b if w[i]+w[i-1]<k else -999)+1 if w[i]<k else -999
    a,b=max(a,b),nb
   z=a if first and w[-1]+w[0]>=k else max(a,b)
   best=max(best,z)
  out.append(max(0,best-k+1))
 return out
def score(w):return sum(x*x for x in deficiencies(w))
assert score(base)==0
w=base.copy();w[rng.choice([i for i,v in enumerate(w) if v>1])]-=1;s=score(w);best=s;steps=0;start=time.monotonic();win=None;events=[]
while time.monotonic()-start<100:
 steps+=1
 if steps%3000==0:
  w=base.copy();w[rng.choice([i for i,v in enumerate(w) if v>1])]-=1;s=score(w)
 i=rng.randrange(n);j=rng.randrange(n)
 if i==j or w[i]<=1 or w[j]>=n:continue
 w[i]-=1;w[j]+=1;z=score(w);temp=.15+1.8*(1-steps%3000/3000)
 if z<=s or rng.random()<math.exp((s-z)/temp):s=z
 else:w[i]+=1;w[j]-=1
 if s<best:best=s;events.append({'steps':steps,'score':s,'w':w.copy()})
 if s==0:win=w.copy();break
out={'n':n,'seed':seed,'cap':cap,'proposals':steps,'best_deficiency_score':best,'witness':win,'events':events,'seconds':time.monotonic()-start,'coverage':'stochastic fixed-sum transfers; no optimality assertion'}
(D/f'outputs/replication-sa-{n}-{seed}.json').write_text(json.dumps(out,indent=2));print(out)
