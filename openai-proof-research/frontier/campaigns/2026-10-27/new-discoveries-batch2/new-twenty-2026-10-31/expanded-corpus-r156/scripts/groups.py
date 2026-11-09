import itertools,functools,json,pathlib
rows=[]
for dims in [(2,2),(2,2,2),(4,2),(2,2,3),(2,2,2,2),(4,2,2),(4,4),(8,2),(2,2,5),(2,2,2,3),(4,2,3)]:
 els=list(itertools.product(*(range(d) for d in dims)))[1:];m=len(els);Z={}
 for k in [3,4,5]:
  for S in itertools.combinations(range(m),k):
   if all(sum(els[i][j] for i in S)%d==0 for j,d in enumerate(dims)):
    mask=sum(1<<i for i in S)
    for i in S:Z.setdefault((i,k),[]).append(mask)
 @functools.lru_cache(None)
 def solve(mask,a,b,c):
  if mask==0:return a==b==c==0
  i=(mask&-mask).bit_length()-1
  for j,k in enumerate([3,4,5]):
   counts=[a,b,c]
   if counts[j]==0:continue
   counts[j]-=1
   for s in Z.get((i,k),[]):
    if s&mask==s and solve(mask^s,*counts):return True
  return False
 counts=[]
 for a in range(m//3+1):
  for b in range(m//4+1):
   if m-3*a-4*b>=0 and (m-3*a-4*b)%5==0:
    c=(m-3*a-4*b)//5;ok=solve((1<<m)-1,a,b,c);assert ok;counts.append([a,b,c])
 rows.append({'cyclic_factors':dims,'order':m+1,'all_345_size_multisets_tested':counts,'zero_sum_subsets':sum(len(v) for (i,k),v in Z.items())//1,'memo_states':solve.cache_info().currsize})
 print(rows[-1],flush=True)
pathlib.Path('outputs/group-search.json').write_text(json.dumps(rows,indent=2))
