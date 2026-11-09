import itertools,json,sys,time
from functools import lru_cache
n,k=map(int,sys.argv[1:]);N=n*(n+1)//2;best=N+1;bestQ=None;sets=0;start=time.time()
for Q in itertools.combinations(range(N),k):
 sets+=1; q=sum(1<<i for i in Q);rows=[(q>>(r*(r+1)//2))&((1<<(r+1))-1) for r in range(n)]
 @lru_cache(None)
 def f(r,a,b):
  if r==n:return 0
  known=rows[r];cost=b-a+1-(known&(((1<<(b-a+1))-1)<<a)).bit_count()
  return cost+max(f(r+1,a,b+1-((known>>b)&1)),f(r+1,a+((known>>a)&1),b+1))
 value=f(0,0,0)
 if value<best:best=value;bestQ=Q
print(json.dumps(dict(n=n,k=k,query_sets=sets,minimax_remaining_uniform=best,best_first_batch=bestQ,seconds=time.time()-start),indent=2))
