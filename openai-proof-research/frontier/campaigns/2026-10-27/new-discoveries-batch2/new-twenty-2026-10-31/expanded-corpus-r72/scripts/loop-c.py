import pathlib,json,sympy as s,math
D=pathlib.Path(__file__).resolve().parents[1]
def patterns(xs,openok=True):
 if not xs:return [()]
 a=xs[0];out=[]
 if openok:
  for p in patterns(xs[1:]):out.append(((a,-1),)+p)
 for j in range(1,len(xs),2):
  for p in patterns(xs[1:j],False):
   for q in patterns(xs[j+1:],openok):out.append(((a,xs[j]),)+p+q)
 return out
def pats(r):
 return [tuple(next((b if a==i else a for a,b in p if i==a or i==b),-1) for i in range(r)) for p in patterns(list(range(r)))]
def asm(n):return math.prod(math.factorial(3*j+1) for j in range(n))//math.prod(math.factorial(n+j) for j in range(n))
out=[]
for r in [3,5,7]:
 P=pats(r);ind={p:j for j,p in enumerate(P)};E=[]
 for a in range(r-1):
  b=a+1;M=s.zeros(len(P))
  for p,j in ind.items():
   q=list(p);c,d=p[a],p[b];f=1
   if c!=b:
    q[a]=b;q[b]=a
    if c>=0:q[c]=d
    if d>=0:q[d]=c
    if c<0 and d<0:f=1 if (a+1)%2 else 2
   M[ind[tuple(q)],j]+=f
  E.append(M)
 B=s.zeros(len(P));S=s.zeros(len(P))
 for p,j in ind.items():
  q=list(p);a=r-1;c=p[a]
  if c>=0:q[c]=-1;q[a]=-1
  B[ind[tuple(q)],j]=1
  if p[0]<0:S[j,j]=1
  else:
   q=list(p);q[p[0]]=-1;q[0]=-1;S[j,j]=-1;S[ind[tuple(q)],j]+=1
 H=(E[0]+S*E[0]*S)/2+sum(E[1:],s.zeros(len(P)))+B;ns=(H-r*s.eye(len(P))).nullspace();rec=dict(r=r,states=len(P),eigenvalue_tested=r,kernel_dimension=len(ns))
 if ns:
  v=ns[0];v=v if sum(v)>0 else -v;v=[s.cancel(t/min(x for x in v if x>0)) for t in v];rec.update(vector=[str(t) for t in v],sum=str(sum(v)),predicted_sum=asm(r//2)*asm((r+1)//2),max=str(max(v)))
 out.append(rec);print(rec,flush=True)
(D/'outputs/loop-c.json').write_text(json.dumps(out,indent=2))
