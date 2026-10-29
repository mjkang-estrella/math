import json,itertools
F=[0,1]
for _ in range(28):F.append(sum(F[-2:]))
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  if x:
   for j,y in enumerate(b):c[i+j]+=x*y
 return c
def qint(a,step=1):return [int(k%step==0) for k in range((a-1)*step+1)]
def Q(A,B):
 d=sum(A)-sum(B);p=[0]*(d+1);p[0]=1
 for a in A:
  for k in range(d,a-1,-1):p[k]-=p[k-a]
 for b in B:
  for k in range(b,d+1):p[k]+=p[k-b]
 return p
def fib(m,n):return Q(F[m+1:m+n+1],F[1:n+1])
rec=0;witness=None
for m in range(2,9):
 for n in range(2,9):
  p=fib(m,n);u=mul(qint(F[m+1],F[n]),fib(m,n-1));v=mul(qint(F[n-1],F[m]),fib(m-1,n));v=[0]*(F[n]*F[m+1])+v
  assert [ (u[t] if t<len(u) else 0)+(v[t] if t<len(v) else 0) for t in range(len(p))]==p
  rec+=1
  for t in range(1,len(p)//2+len(p)%2):
   du=(u[t] if t<len(u) else 0)-(u[t-1] if t-1<len(u) else 0)
   if du<0 and witness is None:
    dv=(v[t] if t<len(v) else 0)-(v[t-1] if t-1<len(v) else 0)
    witness={'m':m,'n':n,'t':t,'D':len(p)-1,'dU':du,'dV':dv,'dTotal':du+dv,'U':u,'V':v}
# exact independent positive generic quotient obstruction
A=[5,5,5,18];B=[1,1,2,3];p=Q(A,B)
num=[1]
for a in A:num=mul(num,qint(a))
den=[1]
for b in B:den=mul(den,qint(b))
assert mul(p,den)==num and min(p)>0 and p==p[::-1] and p[10]>p[11]<p[12]
# Hall obstruction to one-numerator-per-denominator cancellation
hall=None
for n in range(3,16):
 for m in range(n,n+21):
  J=list(range(3,n+1));edges={j:{i for i in range(m+1,m+n+1) if F[i]%F[j]==0} for j in J}
  for size in range(1,len(J)+1):
   for S in itertools.combinations(J,size):
    T=set().union(*(edges[j] for j in S))
    if len(T)<len(S):hall={'m':m,'n':n,'S':S,'neighbors':sorted(T)};break
   if hall:break
  if hall:break
 if hall:break
print(json.dumps({'recurrence_identities':rec,'summand_obstruction':witness,'hall_obstruction':hall,'generic_quotient':{'A':A,'B':B,'p':p}},indent=2))
