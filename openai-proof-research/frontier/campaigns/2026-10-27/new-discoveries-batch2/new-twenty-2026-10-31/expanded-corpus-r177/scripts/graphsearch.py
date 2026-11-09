import pathlib,json,itertools,sys,time,random
D=pathlib.Path(__file__).resolve().parents[1]
# Self-contained labeled degree-sequence realisation enumeration, no graph package.
def realizations(ds,A=None,k=0):
 n=len(ds);A=[0]*n if A is None else A
 if k==n:
  yield A[:];return
 d=ds[k]
 if d<0:return
 vs=[j for j in range(k+1,n) if ds[j]>0]
 for ns in itertools.combinations(vs,d):
  dd=ds[:];aa=A[:];dd[k]=0
  for j in ns:dd[j]-=1;aa[k]|=1<<j;aa[j]|=1<<k
  # Erdos Gallai necessary/sufficient on residual vertices.
  r=sorted(dd[k+1:],reverse=True)
  if sum(r)%2 or any(sum(r[:t])>t*(t-1)+sum(min(x,t) for x in r[t:]) for t in range(1,len(r)+1)):continue
  yield from realizations(dd,aa,k+1)
def trace(A):
 n=len(A);dp=[0]*(1<<n)
 for v in range(n):dp[1<<v]=1<<v
 for mask in range(1,1<<n):
  ends=dp[mask]
  while ends:
   b=ends&-ends;ends-=b;v=b.bit_length()-1;ns=A[v]&~mask
   while ns:
    c=ns&-ns;ns-=c;dp[mask|c]|=c
 return bool(dp[-1])
rows=[]
for m,n in [(2,3),(2,4),(3,4),(3,5),(3,6),(4,4),(4,5)]:
 count=0;fails=[];excluded=0;start=time.monotonic();complete=True
 for A in realizations([m-1]*m+[n-1]*n):
  count+=1
  # Source explicitly excludes disjoint cliques; discard disconnected graphs.
  seen=1
  while True:
   t=seen
   for v in range(m+n):
    if seen>>v&1:seen|=A[v]
   if seen==t:break
  if seen!=(1<<(m+n))-1:excluded+=1;continue
  if not trace(A):fails.append(A);break
  if time.monotonic()-start>16:complete=False;break
 rows.append({'m':m,'n':n,'labeled_realizations':count,'disconnected_excluded':excluded,'complete':complete,'counterexamples':fails});print(rows[-1],flush=True)
(D/'outputs/traceability.json').write_text(json.dumps(rows,indent=2))
