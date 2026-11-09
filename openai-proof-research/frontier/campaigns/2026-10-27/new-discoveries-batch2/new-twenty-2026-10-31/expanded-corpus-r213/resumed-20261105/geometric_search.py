import itertools,random,sys,json,math,time
D=int(sys.argv[1]);trials=int(sys.argv[2]);rng=random.Random(213)
def det(a):
 a=[list(x) for x in a];n=len(a);sgn=1;prev=1
 for k in range(n-1):
  if not a[k][k]:
   j=next((j for j in range(k+1,n) if a[j][k]),None)
   if j is None:return 0
   a[k],a[j]=a[j],a[k];sgn=-sgn
  pivot=a[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):a[i][j]=(a[i][j]*pivot-a[i][k]*a[k][j])//prev
  prev=pivot
 return sgn*a[-1][-1]
def count(P):
 n=len(P);A=[[1]+list(p) for p in P];ch={s:det([A[i] for i in s]) for s in itertools.combinations(range(n),D+1)}
 if 0 in ch.values():return None
 circuits=[]
 for s in itertools.combinations(range(n),D+2):
  coeff=[(-1)**j*ch[s[:j]+s[j+1:]] for j in range(D+2)];pos=sum(1<<s[j] for j,c in enumerate(coeff) if c>0);neg=sum(1<<s[j] for j,c in enumerate(coeff) if c<0);circuits.append((pos,neg))
 full=(1<<n)-1;cross=0
 for a in itertools.combinations(range(1,n),D-1):
  m=1+sum(1<<i for i in a);opp=full^m;cover=0
  for p,q in circuits:
   if p&m==p and q&opp==q or q&m==q and p&opp==p:cover|=p|q
  if cover==full:cross+=1
 return cross
base=count([tuple(i**j for j in range(1,D+1)) for i in range(1,2*D+1)]);print(json.dumps({'d':D,'moment_count':base}),flush=True)
valid=0;best=0;hist={};degenerate=0
for t in range(trials):
 P=set()
 while len(P)<2*D:
  p=list(range(1,D+1));rng.shuffle(p);P.add(tuple(x*rng.choice([-1,1]) for x in p))
 P=sorted(P);c=count(P)
 if c is None:degenerate+=1;continue
 valid+=1;hist[c]=hist.get(c,0)+1
 if c>best:best=c;print(json.dumps({'trial':t,'best':c,'vertices':P}),flush=True)
 if c>base:print('COUNTEREXAMPLE',flush=True);break
print(json.dumps({'d':D,'requested_trials':trials,'valid':valid,'degenerate_rejected':degenerate,'histogram':hist,'best':best,'moment_count':base}),flush=True)
