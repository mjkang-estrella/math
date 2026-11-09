import itertools,pathlib,sys,time,json,random
D=pathlib.Path(__file__).resolve().parents[1]
def concepts():
 E=[(1<<i)|(1<<j)|(1<<k) for i in range(5) for j in range(5,11) for k in range(j+1,11)];m=len(E);allbits=(1<<m)-1
 N=[sum(1<<j for j,f in enumerate(E) if e&f) for e in E]
 def nbr(a):
  b=allbits
  while a:
   bit=a&-a;a-=bit;b&=N[bit.bit_length()-1]
  return b
 def cls(a):return nbr(nbr(a))
 hit=[sum(1<<j for j,e in enumerate(E) if e&c) for c in range(2048) if c.bit_count()==4]
 a=cls(0);count=valid=0;t=time.monotonic();complete=False;bad=None
 while time.monotonic()-t<105:
  count+=1;b=nbr(a);sa=sb=0
  for i,e in enumerate(E):
   if a>>i&1:sa|=e
   if b>>i&1:sb|=e
  if sa==sb==2047:
   valid+=1
   if not any((a|b)&~h==0 for h in hit):bad=[a,b];break
  for i in range(m-1,-1,-1):
   if not(a>>i&1):
    low=(1<<i)-1;c=cls((a&low)|(1<<i))
    if c&low==a&low:a=c;break
  else:complete=True;break
  if count%100000==0:print(count,valid,flush=True)
 res=dict(method='Galois NextClosure exact enumeration',n=11,pin_size=5,r=3,s=3,closed_pairs=count,valid_same_support=valid,complete=complete,counterexample=bad,wall=time.monotonic()-t)
 print(res);(D/'concepts11-search.json').write_text(json.dumps(res,indent=2)+'\n')
def cyclic(p):
 valid=leaves=0;t=time.monotonic();complete=True
 def order(rem,s,seen):
  if rem.bit_count()==1:return True
  opts=rem
  while opts:
   bit=opts&-opts;opts-=bit;i=bit.bit_length()-1;w=(s+i)%p
   if not seen>>w&1 and order(rem^bit,w,seen|1<<w):return True
  return False
 for digits in itertools.product((0,1,-1),repeat=(p-1)//2):
  leaves+=1
  X=[(i+1)*d%p for i,d in enumerate(digits) if d]
  if len(X)>=3 and sum(X)%p==0:
   valid+=1;rem=sum(1<<i for i in X);first=X[0]
   if not order(rem^(1<<first),first,1|(1<<first)):print('FAIL',X);break
  if leaves%100000==0 and time.monotonic()-t>105:complete=False;break
 res=dict(p=p,ternary_assignments=leaves,valid_zero_sum_sets=valid,complete=complete,wall=time.monotonic()-t)
 print(res);(D/f'cyclic-{p}.json').write_text(json.dumps(res,indent=2)+'\n')
def cube(n,anti,trials):
 E=[(v,v^(1<<i)) for v in range(1<<n) for i in range(n) if not v>>i&1];idx={tuple(sorted(e)):i for i,e in enumerate(E)};full=(1<<n)-1;reps={};orient={};k=0
 for j,(v,w) in enumerate(E):
  if j in reps:continue
  reps[j]=k;orient[j]=0
  if anti:
   t=idx[tuple(sorted((v^full,w^full)))];reps[t]=k;orient[t]=1
  k+=1
 paths=[]
 for start in range(1<<n):
  for a in itertools.permutations(range(n)):
   v=start;path=[]
   for i in a:w=v^(1<<i);j=idx[tuple(sorted((v,w)))];path.append((reps[j],orient[j]));v=w
   paths.append(path)
 rng=random.Random(231);count=0
 for z in range(trials or (1<<k)):
  mask=rng.getrandbits(k) if trials else z;count+=1
  for path in paths:
   cols=[(mask>>j&1)^o for j,o in path]
   if sum(a!=b for a,b in zip(cols,cols[1:]))<=(0 if anti else 1):break
  else:print('FAIL',n,anti,mask);return
 res=dict(n=n,antipodal=anti,assignments=count,exhaustive=not bool(trials),counterexample=None)
 print(res,flush=True);(D/f'cube-{n}-{anti}-{trials}.json').write_text(json.dumps(res,indent=2)+'\n')
if sys.argv[1]=='concepts':concepts()
elif sys.argv[1]=='cyclic':cyclic(int(sys.argv[2]))
else:
 cube(3,False,0);cube(4,True,0);cube(4,False,100000);cube(5,True,20000)
