import numpy as np,math,pathlib,json,random
D=pathlib.Path(__file__).resolve().parents[1];random.seed(105);out=[]
for n in [10001,12000]:
 prime=np.ones(2*n+1,dtype=bool);prime[:2]=False
 for p in range(2,math.isqrt(2*n)+1):
  if prime[p]:prime[p*p::p]=False
 js=np.arange(n+1);odd=js%2==1
 for near in [False,True]:
  allowed=prime.copy();allowed[2]=False
  if near:allowed[1]=True
  adj=[]
  for i in range(n+1):
   row=allowed[i+js]&allowed[np.abs(i-js)];row[i]=False
   if near:row[0]=False
   adj.append(int.from_bytes(np.packbits(row,bitorder='little').tobytes(),'little'))
  sources=[1,2,3,n//2,n-2,n-1,n]+random.sample(range(1,n+1),13);records=[];full=(1<<(n+1))-1-(1 if near else 0)
  for s in sources:
   seen=1<<s;front=seen;depth=0;sizes=[1]
   while front and seen!=full:
    nxt=0
    while front:
     bit=front&-front;front-=bit;nxt|=adj[bit.bit_length()-1]
    front=nxt&~seen;seen|=front;depth+=1;sizes.append(front.bit_count())
   records.append(dict(source=s,reachable=seen.bit_count(),eccentricity=depth,layer_sizes=sizes))
  z=dict(n=n,near=near,vertices=n if near else n+1,sources=records,limitation='Selected-source eccentricities, not all-pairs diameter. Beyond 10000 only at these two orders.');out.append(z);print(n,near,max(r['eccentricity']for r in records),flush=True);(D/'outputs/goldbach-large.json').write_text(json.dumps(out,indent=2))
