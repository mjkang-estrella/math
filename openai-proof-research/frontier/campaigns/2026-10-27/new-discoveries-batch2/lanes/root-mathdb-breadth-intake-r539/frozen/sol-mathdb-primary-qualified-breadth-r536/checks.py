import pathlib,json,math
P=pathlib.Path(__file__).resolve().parent
# Exact half-up rounding, not floating point; finite factor occurrence only.
a=b=1;m=[]
for n in range(2001):m.append((2*a+b)//(2*b));a*=3;b*=2
t=[2*m[i+1]-3*m[i] for i in range(2000)]
factors=[dict(k=k,observed=len({tuple(t[i:i+k]) for i in range(len(t)-k+1)}),claimed=3**(k+1)-2**(k+1)) for k in range(1,9)]
def cb(n,k):return math.comb(n,k) if 0<=k<=n else 0
def size(n,p,q):return sum(cb(n,j)*cb(p,j)*cb(q+n-j,n-j) for j in range(n+1))
violations=[];cases=0
for n in range(13):
 for d in range(21):
  v=size(n,d//2,(d+1)//2)
  for p in range(d+1):
   cases+=1
   if size(n,p,d-p)>v:violations.append([n,d,p])
r={'steering':{'terms':2000,'rounding':'half up exactly in integers','factor_counts':factors,'limit':'Occurrence lower bounds only; missing factors may occur later; no all-k proof.'},'anticode_unbalanced_family':{'n_range':[0,12],'D_range':[0,20],'comparisons':cases,'larger_than_balanced':violations,'limit':'Only source-defined simplex-shaped competitors; not all anticodes.'},'star_kernel_bound':[{'k':k,'max_antichain':cb(k,k//2),'kernel_vertex_bound':k+cb(k,k//2)} for k in range(1,10)]}
(P/'bounded-checks.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
