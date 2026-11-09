import pathlib,itertools,math,collections,json
D=pathlib.Path(__file__).resolve().parents[1]
def count(sh):
 c=collections.Counter();m=len(sh);N=sum(sh);a=[[] for _ in sh]
 def rec(r,rem):
  if r==m-1:
   a[r]=rem;inv=0
   for u in range(m):
    for v in range(u+1,m):
     for j in range(min(sh[u],sh[v])):
      s,l=(u,v) if a[u][j]<a[v][j] else (v,u)
      inv += (s>l) if j+1>=sh[s] or j+1>=sh[l] else (a[s][j+1]>a[l][j+1])
   c[inv]+=1;return
  for sel in itertools.combinations(rem,sh[r]):
   a[r]=sel;ss=set(sel);rec(r+1,tuple(x for x in rem if x not in ss))
 rec(0,tuple(range(1,N+1)));return [c[i] for i in range(max(c)+1)]
rows=[]
for m,n in [(m,n) for m in range(2,9) for n in range(1,7) if m*n<=12 and math.factorial(m*n)//math.factorial(n)**m<=400000]:
 a=count([n]*m);b=count([n+1]+[n]*(m-2)+[n-1]);fail=[i for i in range(n*(m-2)*(m-1)//2+1,len(a)) if a[i]!=(b[i-m+1] if 0<=i-m+1<len(b) else 0)]
 z={'m':m,'n':n,'row_standard_count':sum(a),'A':a,'B':b,'failures':fail};rows.append(z);print(json.dumps(z),flush=True);(D/'outputs/tableaux-exhaustive.json').write_text(json.dumps(rows,indent=2))
