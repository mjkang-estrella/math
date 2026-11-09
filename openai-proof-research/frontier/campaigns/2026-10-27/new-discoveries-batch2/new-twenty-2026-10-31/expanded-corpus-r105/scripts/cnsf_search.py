import pathlib,itertools,random,json,sys,hashlib
from cnsf_source import compositions_with_ones,iso,sym
D=pathlib.Path(__file__).resolve().parents[1];random.seed(105)
def sig(p):
 n=len(p)+1;t=[p[0]]+[p[i]-p[i-1] for i in range(1,n-1)]+[-p[-1]];out=[]
 pref={}
 for x in [-2,-1,0,1,2]:
  q=[0]
  for z in t:q.append(q[-1]+(z>x))
  pref[x]=q
 for k in range(2,n):
  counts=[0]*(n-k+1)
  for i in range(n-k+1):
   x=p[k-1] if i==0 else -p[n-k-1] if i==n-k else p[i+k-1]-p[i-1]
   q=pref[x];a=q[i]+q[n]-q[i+k];counts[a]+=1
  out.extend(counts)
 return bytes(out)
mode=sys.argv[1];out=[]
for n in ([3,4,5,6,7,8,9,10,11,12,13,14,15] if mode=='small' else [int(sys.argv[2])] if len(sys.argv)>2 else [25,26,32,40]):
 seen={};coll=[];ct=0
 if mode=='small':seq=itertools.product([-1,1],repeat=n-1)
 else:
  def gen():
   for j in range(5):
    for turns in itertools.combinations(range(1,n-1),j):
     p=[1]*(n-1)
     for i in range(1,n-1):p[i]=-p[i-1] if i in turns else p[i-1]
     yield tuple(p)
     yield tuple(-x for x in p)
   for _ in range(1000):yield tuple(random.choice([-1,1]) for _ in range(n-1))
  seq=gen()
 for p in seq:
  if (n%2 and sym(p)) or p>iso(p):continue
  s=sig(p);ct+=1
  if s in seen and seen[s]!=p:coll.append([seen[s],p])
  seen[s]=p
 z=dict(n=n,tested=ct,distinct=len(seen),collisions=coll[:10]);out.append(z);print(z,flush=True);(D/f'outputs/cnsf-{mode}-{sys.argv[2] if len(sys.argv)>2 else "all"}.json').write_text(json.dumps(out,indent=2))
