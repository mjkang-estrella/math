import random,json,pathlib,sys,time,math
D=pathlib.Path(__file__).resolve().parents[1]
seed=int(sys.argv[1]); rng=random.Random(seed)
def family(n,r,s=1):
 types=[0]*s+list(range(1,r))+[r]*(n-2*r+2-s)+list(range(r+1,2*r))
 return [sum(1<<j for j,b in enumerate(types) if i!=j and (a==b or (a//r==b//r and b%r<=a%r+1) or (a//r!=b//r and b%r==0))) for i,a in enumerate(types)]
def stats(a):
 n=len(a);full=(1<<n)-1;w=0;ec=[]
 for i in range(n):
  seen=1<<i;front=seen;ecc=0
  while seen!=full and front:
   z=0
   while front:
    bit=front&-front;front-=bit;z|=a[bit.bit_length()-1]
   front=z&~seen;seen|=front;ecc+=1;w+=ecc*front.bit_count()
  if seen!=full:return 100000, [0]*n
  ec.append(ecc)
 return w,ec
def sig(a):
 return sorted((x.bit_count(),sum((v>>i)&1 for v in a)) for i,x in enumerate(a))
out=[]
for r,n in [(3,n) for n in range(6,13)]+[(4,n) for n in range(8,13)]+[(5,10),(5,11),(5,12)]:
 target=stats(family(n,r))[0];signatures=[sig(family(n,r,s)) for s in range(1,(n-2*r+2)//2+1)]
 best=10**9; distinct=set();checks=0; anomal=[]
 for restart in range(10):
  a=family(n,r);w,ec=stats(a)
  def energy(w,ec):return w+20*sum(max(0,r-e)**2 for e in ec)+20*max(0,min(ec)-r)**2
  en=energy(w,ec)
  for it in range(2500):
   u=rng.randrange(n);v=rng.randrange(n-1);v+=v>=u;a[u]^=1<<v
   w2,e2=stats(a);en2=energy(w2,e2);checks+=1
   temp=0.25+2.0*(1-it/2500)
   if en2<=en or rng.random()<math.exp(max(-700,(en-en2)/temp)):w,ec,en=w2,e2,en2
   else:a[u]^=1<<v
   if min(ec)==r and w<100000:
    best=min(best,w)
    if w<=target:
     distinct.add(tuple(a))
     if w<target or sig(a) not in signatures:
      anomal.append({'adj':a[:],'W':w,'ecc':ec[:],'degree_sig':sig(a)});break
  if anomal:break
 record={'r':r,'n':n,'target':target,'best':best,'toggle_proposals':checks,'labelled_extremal_states':len(distinct),'anomalies':anomal}
 print(json.dumps(record),flush=True);out.append(record)
 if anomal:break
(D/f'outputs/digraph-{seed}.json').write_text(json.dumps(out,indent=2)+'\n')
