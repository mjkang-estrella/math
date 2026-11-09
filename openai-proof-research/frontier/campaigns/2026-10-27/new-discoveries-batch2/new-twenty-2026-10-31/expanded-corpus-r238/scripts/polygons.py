import random,math,time,json,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(238)
def orient(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def cross(a,b,c,d):return orient(a,b,c)*orient(a,b,d)<0 and orient(c,d,a)*orient(c,d,b)<0
def simple(p):
 n=len(p)
 return all(not cross(p[i],p[(i+1)%n],p[j],p[(j+1)%n]) for i in range(n) for j in range(i+1,n) if (i+1)%n!=j and (j+1)%n!=i)
def gp(a,b):
 p=a+b
 return all(orient(p[i],p[j],p[k]) for i in range(len(p)) for j in range(i+1,len(p)) for k in range(j+1,len(p)))
def score(a,b):return sum(cross(a[i],a[(i+1)%len(a)],b[j],b[(j+1)%len(b)]) for i in range(len(a)) for j in range(len(b)))
def init(n):
 p=[(rng.randrange(-1000,1001),rng.randrange(-1000,1001)) for _ in range(n)];x=sum(z[0] for z in p)/n;y=sum(z[1] for z in p)/n
 return sorted(p,key=lambda z:math.atan2(z[1]-y,z[0]-x))
out=[]
for n,m in [(5,5),(5,7),(7,7),(7,9),(9,9)]:
 t0=time.monotonic();iterations=0;valid=0;best=-1
 while time.monotonic()-t0<18:
  if iterations%1000==0:
   while True:
    a,b=init(n),init(m)
    if simple(a) and simple(b) and gp(a,b):break
   s=score(a,b)
  iterations+=1;aa,bb=a[:],b[:];p=rng.choice([aa,bb]);i=rng.randrange(len(p));kind=rng.randrange(3)
  if kind==0:
   j=rng.randrange(len(p));i,j=sorted((i,j));p[i:j+1]=reversed(p[i:j+1])
  elif kind==1:p[i]=(p[i][0]+rng.randrange(-150,151),p[i][1]+rng.randrange(-150,151))
  else:p[i]=(rng.randrange(-1000,1001),rng.randrange(-1000,1001))
  if not simple(aa) or not simple(bb) or not gp(aa,bb):continue
  valid+=1;s1=score(aa,bb);temp=2.5*(1-(iterations%1000)/1000)+.05
  if s1>=s or rng.random()<math.exp((s1-s)/temp):a,b,s=aa,bb,s1
  if s1>best:best=s1;ba,bc=aa,bb
  if best>n*m-n-m+3:break
 row=dict(m=n,n=m,proposals=iterations,valid_proposals=valid,best_crossings=best,bound=n*m-n-m+3,P=ba,Q=bc,seed=238,seconds=time.monotonic()-t0);out.append(row);print(json.dumps(row),flush=True);(D/'polygon-coverage.json').write_text(json.dumps(out,indent=2)+'\n')
