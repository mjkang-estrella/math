import itertools,json
patterns=[a for a in itertools.product(range(3),repeat=3) if set(a)==set(range(max(a)+1))]
out=[]
for n in range(5,101):
 m=n-3;best=[-10**9,-10**9]
 for a in patterns:
  f=[2*x+1 for x in a];k=max(a)+1
  X=lambda i,j:int(f[i]<=f[j])
  const=[X(0,1)+X(2,1)-X(0,2)-X(2,0),-X(0,1)-X(0,2)-X(2,0)-X(2,1)]
  for typ in range(2):
   dp=[0]+[-10**9]*m
   for pos in range(2*k+1):
    sc=int(f[0]<=pos)+int(pos<=f[0])+int(f[2]<=pos)+int(pos<=f[2])+(-1 if typ==0 else 1)*int(pos<=f[1])
    dp=[max(dp[z-t]+sc*t-(t*(t-1)//2 if pos%2 else 0) for t in range(z+1)) for z in range(m+1)]
   best[typ]=max(best[typ],dp[m]+const[typ]-m*(m-1)//2)
 bounds=[4-(n-5)*(n-6)//2,5-(n-6)*(n-7)//2]
 assert best==bounds,(n,best,bounds)
 out.append(dict(n=n,maximum_a=best[0],maximum_e=best[1],bounds=bounds))
 print(out[-1],flush=True)
json.dump({'scope':'validity only; intended single sum of fixed-unfixed arcs; 8 rows reduce to a,e by relabeling and reversal; not literal double sum and not facet rank','rows':out},open('outputs/t3.json','w'),indent=2)
