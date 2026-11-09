import functools,itertools,json,time
from pathlib import Path
start=time.monotonic()
@functools.lru_cache(None)
def count(ds,signed):
 if not ds:return 1
 d,*rest=ds; total=0
 for diag in range(min(d,2)+1):
  for es in itertools.product(*(range(min(x,2,d-diag)+1)for x in rest)):
   if sum(es)!=d-diag:continue
   weight=(2**sum(x>0 for x in es) if signed else 1)*(2 if signed and diag==2 else 1)
   total+=weight*count(tuple(sorted(x-e for x,e in zip(rest,es))),signed)
 return total
r={'labelled_unsigned_without_connectivity_filter':count((3,)*8,False),'labelled_signed_fixed_semi_sign_without_connectivity_filter':count((3,)*8,True),'seconds':time.monotonic()-start,'memo':str(count.cache_info()),'method':'Exact labelled symmetric integer matrix count by row residual degree recursion; |offdiagonal| <= 2, |diagonal| <= 2, absolute row sum 3; diagonal 1 sign fixed positive. No connectivity or trivial-character pretest.'}
p=Path(__file__).resolve().parents[1];(p/'logs/case-counts.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
