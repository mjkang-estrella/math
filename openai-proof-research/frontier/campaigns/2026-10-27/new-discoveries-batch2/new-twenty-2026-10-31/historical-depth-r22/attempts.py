import resource,os,itertools,collections,math,json,time
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3)); resource.setrlimit(resource.RLIMIT_CPU,(80,80));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
def sc(p):
 s=[];out=[];cuts=[]
 for a in p:
  while any(a<s[j]<s[j+1] for j in range(len(s)-1)):
   out.append(s.pop(0))
  s.insert(0,a)
 return tuple(out+s)
def block(p):
 blocks=[]
 for a in p[1:]:
  if not blocks or a<blocks[-1][0]: blocks.append([a])
  else:blocks[-1].append(a)
 return tuple(x for b in blocks for x in reversed(b))+(p[0],)
for n in range(2,9):
 c=collections.Counter(); mismatch=0
 for p in itertools.permutations(range(1,n+1)):
  q=sc(p);c[q]+=1
  if p[0]==n and q!=block(p):mismatch+=1
 print('stack',n,'max',max(c.values()),'expected',2**(n-2),'block_mismatch',mismatch,'maximizers',sum(v==max(c.values()) for v in c.values()),flush=True)
 # Source adjacent-value claims independently tested (induction-free exact equality for deletion).
 for q,v in c.items():
  a=q[-1]
  if a==n:continue
  if q[-2]!=a+1:
   qp=tuple(a+1 if x==a else a if x==a+1 else x for x in q);assert v<=c[qp]
  else: assert v<=2**max(0,n-3)
# exact f33 minimization, source 4.17, beyond relying on single balanced substitution
for n in range(3,66):
 f=[math.factorial(i) for i in range(n+1)]
 def v(t,x,y):
  return f[t+x]*f[n-t-x]+f[t+y]*f[n-t-y]+2*f[t+x+y]*f[n-t-x-y]-2*f[t+x]*f[y]*f[n-t-x-y]-2*f[t+y]*f[x]*f[n-t-x-y]
 cand=v((n-2)//2,1,1);best=min((v(t,x,y),t,x,y) for t in range(n-2) for x in range(1,n-t-1) for y in range(x,n-t-x))
 print('lattice',n,'balanced_min',best[0]==cand,'argmin',best[1:],flush=True)
# structural normalization in spectral problem: a,b,c>=1, sum=n, each<=n-4.
# Factor every polynomial only for n<=30; a factor is not a common Perron root certificate.
import sympy as S
X=S.Symbol('X')
for n in range(6,31):
 reduc=[]
 for a in range(1,n//3+1):
  for b in range(a,(n-a)//2+1):
   c=n-a-b
   if c>n-4:continue
   p=X**n-X**a-X**b-X**c-2;fac=S.factor_list(p)[1]
   if len(fac)>1:reduc.append(dict(abc=[a,b,c],factors=[[str(q),e] for q,e in fac]))
 print('spectral',n,json.dumps(reduc),flush=True)
