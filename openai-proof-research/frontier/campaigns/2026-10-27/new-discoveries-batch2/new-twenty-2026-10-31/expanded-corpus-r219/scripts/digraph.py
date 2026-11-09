import itertools,json,random,sys
n=int(sys.argv[1]);mode=sys.argv[2];full=(1<<n)-1
counts=dict(generated=0,min_degrees=0,neighborhood_cyclic=0,strong=0,counterexamples=0)
def strong(a,S):
 r=S&-S
 while True:
  t=r
  for i in range(n):
   if r>>i&1:t|=a[i]&S
  if t==r:break
  r=t
 if r!=S:return False
 r=S&-S
 while True:
  t=r
  for i in range(n):
   if S>>i&1 and a[i]&r:t|=1<<i
  if t==r:break
  r=t
 return r==S
def acyclic(a,S):
 while S:
  rem=sum(1<<i for i in range(n) if S>>i&1 and not a[i]&S)
  if not rem:return False
  S^=rem
 return True
def check(a):
 counts['generated']+=1
 ins=[sum(1<<j for j in range(n) if a[j]>>i&1) for i in range(n)]
 if any(x.bit_count()<2 for x in ins):return
 counts['min_degrees']+=1
 if any(acyclic(a,x) for x in a+ins):return
 counts['neighborhood_cyclic']+=1
 if not strong(a,full):return
 counts['strong']+=1
 for S in range(1,full):
  if (full^S).bit_count()>=2 and acyclic(a,S) and not strong(a,full^S):return
 counts['counterexamples']+=1;print('WITNESS',a,flush=True)
if mode=='exhaustive':
 choices=[[S for S in range(full+1) if not S>>i&1 and S.bit_count()>=2] for i in range(n)]
 for a in itertools.product(*choices):
  if sum(x.bit_count() for x in a)<3*n-3:check(list(a))
else:
 rng=random.Random(219+n);arcs=[(i,j) for i in range(n) for j in range(n) if i!=j]
 for it in range(int(sys.argv[3])):
  a=[0]*n
  for i,j in rng.sample(arcs,3*n-4):a[i]|=1<<j
  if all(x.bit_count()>=2 for x in a):check(a)
print(json.dumps(dict(n=n,mode=mode,counts=counts)),flush=True)
