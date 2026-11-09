import itertools,json,sys,time
n,k=map(int,sys.argv[1:]);N=n*(n+1)//2
best=N+1;bestQ=None;sets=answers=0;start=time.time()
def residual(q,a):
 reach=1;total=off=0
 for row in range(1,n+1):
  mask=(1<<row)-1;known=(q>>off)&mask;right=(a>>off)&mask
  total+=(reach&~known).bit_count()
  reach=(reach&(~known|~right))|((reach&(~known|right))<<1)
  off+=row
 return total
for Q in itertools.combinations(range(N),k):
 sets+=1;q=sum(1<<j for j in Q);a=q;worst=0
 while True:
  answers+=1;worst=max(worst,residual(q,a))
  if worst>=best:break
  if not a:
   best=worst;bestQ=Q;break
  a=(a-1)&q
print(json.dumps(dict(n=n,k=k,query_sets=sets,answers_evaluated=answers,minimax_remaining_unknown_reachable=best,best_first_batch=bestQ,seconds=time.time()-start),indent=2))
