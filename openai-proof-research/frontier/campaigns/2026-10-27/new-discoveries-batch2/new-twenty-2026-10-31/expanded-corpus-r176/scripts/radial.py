import pathlib,json,random,time,math,sys
D=pathlib.Path(__file__).resolve().parents[1];d=int(sys.argv[1]);seed=int(sys.argv[2]);rng=random.Random(seed);n=d*d+1;base=d+1;L=d*(d-1);full=(1<<n)-1
a=[0]*n

def edge(u,v):a[u]|=1<<v;a[v]|=1<<u
for i in range(d):
 edge(0,i+1)
 for j in range(d-1):edge(i+1,base+i*(d-1)+j)
p=list(range(base,n));rng.shuffle(p)
for i in range(L):
 for k in range(1,(d-1)//2+1):edge(p[i],p[(i+k)%L])
 if (d-1)%2:edge(p[i],p[(i+L//2)%L])
def score():
 total=0;bad=0
 for v in range(n):
  one=a[v];two=one;bs=one
  while bs:
   b=bs&-bs;bs-=b;two|=a[b.bit_length()-1]
  two&=~(one|1<<v);three=0;bs=two
  while bs:
   b=bs&-bs;bs-=b;three|=a[b.bit_length()-1]
  three&=full&~(one|two|1<<v)
  unseen=n-1-one.bit_count()-two.bit_count()-three.bit_count()
  bad+=unseen;total+=one.bit_count()+2*two.bit_count()+3*three.bit_count()+4*unseen
 return total-1000*bad,total,bad
cur=score();best=0;attempts=0;valid=0;accepted=0;start=time.monotonic();target=3*d**4-4*d**3+3*d*d-d
while time.monotonic()-start<100:
 attempts+=1;u,v,x,y=rng.sample(range(base,n),4)
 if not (a[u]>>v&1 and a[x]>>y&1) or a[u]>>x&1 or a[v]>>y&1:continue
 for z,w in [(u,v),(x,y),(u,x),(v,y)]:a[z]^=1<<w;a[w]^=1<<z
 z=score()
 if z[2]==0:
  valid+=1
  if z[1]>best:
   best=z[1];print('best',best,'target',target,'attempt',attempts,flush=True)
   if best>target:
    (D/f'outputs/radial-witness-{d}-{seed}.json').write_text(json.dumps({'d':d,'seed':seed,'status':best,'target':target,'adjacency':a},indent=2));break
 temp=1.+6*(1-(attempts%20000)/20000)
 if z[0]>=cur[0] or rng.random()<math.exp(max(-700,(z[0]-cur[0])/temp)):cur=z;accepted+=1
 else:
  for z,w in [(u,v),(x,y),(u,x),(v,y)]:a[z]^=1<<w;a[w]^=1<<z
out={'degree':d,'seed':seed,'vertices':n,'attempts':attempts,'valid_evaluations':valid,'accepted':accepted,'best_status':best,'target':target,'seconds':time.monotonic()-start,'scope':'heuristic leaf-regular graph switches with fixed radius-two Moore tree; not exhaustive; independent circulant start'}
(D/f'outputs/radial-{d}-{seed}.json').write_text(json.dumps(out,indent=2)+'\n');print(out,flush=True)
