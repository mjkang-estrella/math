import sympy as s,itertools,pathlib,json,math
D=pathlib.Path(__file__).resolve().parents[1]
def pats(N):
 def rec(xs):
  if not xs:return [()]
  a=xs[0];out=[]
  for k in range(1,len(xs),2):
   b=xs[k]
   for p in rec(xs[1:k]):
    for q in rec(xs[k+1:]):out.append(((a,b),)+p+q)
  return out
 return [tuple(next(b if a==i else a for a,b in p if a==i or b==i) for i in range(N)) for p in rec(list(range(N)))]
def asm(n):return math.prod(math.factorial(3*j+1) for j in range(n))//math.prod(math.factorial(n+j) for j in range(n))
out=[]
for n in range(1,7):
 N=2*n;P=pats(N);index={p:i for i,p in enumerate(P)};H=s.zeros(len(P))
 for p,j in index.items():
  for a in range(N):
   b=(a+1)%N;q=list(p)
   if p[a]!=b:
    c,d=p[a],p[b];q[a]=b;q[b]=a;q[c]=d;q[d]=c
   H[index[tuple(q)],j]+=1
 v=(H-N*s.eye(len(P))).nullspace()[0];v=[s.cancel(x/min(v)) for x in v];assert all(x>0 for x in v)
 out.append(dict(n=n,states=len(P),max=str(max(v)),predicted=asm(n-1),sum=str(sum(v)),vector=[str(x) for x in v]));print(out[-1],flush=True)
(D/'outputs/loop-even.json').write_text(json.dumps(out,indent=2))
