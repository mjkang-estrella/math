import sys,collections,json,hashlib
n=int(sys.argv[1]);A=collections.Counter();B=collections.Counter();counts=[0,0]
def record(p,kind):
 small=n+1;large=-1;rmin=rmax=0
 for x in p[::-1]:
  if x<small:rmin+=1;small=x
  if x>large:rmax+=1;large=x
 if kind==0:
  low=n+1;lmin=0
  for x in p:
   if x<low:lmin+=1;low=x
  A[rmin,lmin,rmax,sum(p[i]<p[i+1] for i in range(n-1))]+=1
 else:B[p.count(0),sum(x==i for i,x in enumerate(p)),rmin,n-len(set(p))]+=1
 counts[kind]+=1
def perm(p,rem,ascpairs,bound):
 if not rem:record(p,0);return
 for x in rem:
  if x>bound:continue
  nb=min([bound]+[b for a,b in ascpairs if x<a]);ap=ascpairs
  if p and p[-1]<x:ap=ascpairs+[(p[-1],x)]
  perm(p+[x],[y for y in rem if y!=x],ap,nb)
def inv(p,seen,repeated):
 if len(p)==n:record(p,1);return
 for x in range(max(0,repeated),len(p)+1):inv(p+[x],seen|1<<x,max(repeated,x) if seen>>x&1 else repeated)
perm([],list(range(n)),[],n);print('permutations',sum(A.values()),flush=True)
inv([],0,-1);bad=[(k,A[k],B[k]) for k in set(A)|set(B) if A[k]!=B[k]]
print(json.dumps(dict(n=n,counts=counts,bad_first=bad[:10],bad_count=len(bad),histA_sha256=hashlib.sha256(repr(sorted(A.items())).encode()).hexdigest(),histB_sha256=hashlib.sha256(repr(sorted(B.items())).encode()).hexdigest())),flush=True)
