import pathlib,json,time,random,math,sys
D=pathlib.Path(__file__).resolve().parents[1];cyc=bool(int(sys.argv[1]));rng=random.Random(1930+cyc);n=16
p=D/('outputs/replication-sa-16-194.json' if cyc else 'outputs/replication-path-sa-16-195.json');base=json.loads(p.read_text())['witness']
def score(w):
 s=0
 for k in range(2,n+1):
  best=-1
  for f in [0,1]:
   if f and w[0]>=k:continue
   a,b=(0,-999) if f==0 else (-999,1)
   for i in range(1,n):
    nb=max(a,b if w[i]+w[i-1]<k else -999)+1 if w[i]<k else -999
    a,b=max(a,b),nb
   z=a if cyc and f and w[-1]+w[0]>=k else max(a,b);best=max(best,z)
  s+=max(0,best-k+1)**2
 return s
assert score(base)==0
start=time.monotonic();steps=0;wins=[base.copy()];best=999
w=base.copy();w[rng.choice([i for i,z in enumerate(w) if z>1])]-=1;s=score(w)
while time.monotonic()-start<105:
 steps+=1
 if steps%4000==0:
  w=base.copy();w[rng.choice([i for i,z in enumerate(w) if z>1])]-=1;s=score(w)
 i=rng.randrange(n);j=rng.randrange(n)
 if i==j or w[i]<=1 or w[j]>=n:continue
 w[i]-=1;w[j]+=1;z=score(w);temp=.1+1.5*(1-steps%4000/4000)
 if z<=s or rng.random()<math.exp((s-z)/temp):s=z
 else:w[i]+=1;w[j]-=1
 best=min(best,s)
 if s==0:
  base=w.copy();wins.append(base.copy());print('new upper bound',sum(base),base,flush=True);best=999
  w[rng.choice([i for i,z in enumerate(w) if z>1])]-=1;s=score(w)
(D/f'outputs/replication-descent-{int(cyc)}.json').write_text(json.dumps({'n':n,'cycle':cyc,'feasible_vectors':wins,'proposals':steps,'best_failed_score':best,'seconds':time.monotonic()-start,'coverage':'local search, no lower bound'},indent=2))
