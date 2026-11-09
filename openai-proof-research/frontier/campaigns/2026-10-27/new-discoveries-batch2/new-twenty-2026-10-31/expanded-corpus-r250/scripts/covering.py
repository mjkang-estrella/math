import itertools,json,random,math,time
start=time.monotonic();random.seed(250)
def digits(a,t,n):
 out=[]
 for _ in range(n):out.append(a%t);a//=t
 return out
def le(a,b):return all(x<=y for x,y in zip(a,b))
for t,n in [(2,5),(2,6),(2,7),(2,8),(3,4),(3,5),(4,4),(5,4)]:
 q=t**n-1;ds=[digits(a,t,n) for a in range(q)];ps={pow(t,k,q) for k in range(n)};tested=0;maxpairs=0
 for d in range(1,q):
  if d in ps:continue
  imgs=[(a*d)%q for a in range(q)];found=False;pairs=0
  for a in range(1,q):
   for b in range(a+1,q):
    if le(ds[a],ds[b]):
     pairs+=1
     if imgs[a]!=imgs[b] and le(ds[imgs[b]],ds[imgs[a]]):found=True;break
   if found:break
  assert found,(t,n,d)
  tested+=1;maxpairs=max(maxpairs,pairs)
 print(json.dumps(dict(t=t,n=n,all_d=tested,max_comparable_pairs_tested=maxpairs,wall=time.monotonic()-start)),flush=True)
# Witness-only sampling outside published 3e9 range. No inference from absence.
for t,n in [(83,5),(100,5),(121,5),(10,10),(2,33)]:
 q=t**n-1;pows=[t**j for j in range(n)];powers={pow(t,j,q) for j in range(n)};tested=0;foundcount=0;missing=[]
 for d in [*range(2,202),*[random.randrange(2,q) for _ in range(100)]]:
  if d in powers:continue
  tested+=1;found=False
  for _ in range(2000):
   a=random.randrange(1,q);j=random.randrange(n)
   if a//pows[j]%t==t-1:continue
   b=a+pows[j]
   if b>=q:continue
   da,db=(d*a)%q,(d*b)%q
   if da!=db and le(digits(db,t,n),digits(da,t,n)):
    found=True;break
  if found:foundcount+=1
  else:missing.append(d)
 print(json.dumps(dict(t=t,n=n,modulus=q,sampled_d=tested,witnessed=foundcount,unresolved_sample=missing,wall=time.monotonic()-start)),flush=True)
