import pathlib,json,itertools,random,time
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
def witness(lists):
 w=[];nodes=0
 def go(j):
  nonlocal nodes
  nodes+=1
  if j==len(lists):return w[:]
  for x in lists[j]:
   w.append(x);n=len(w)
   if all(w[n-2*k:n-k]!=w[n-k:] for k in range(1,n//2+1)):
    res=go(j+1)
    if res is not None:return res
   w.pop()
  return None
 return go(0),nodes
t=time.monotonic();alphabet=list(itertools.combinations(range(5),3));count=0;maxnodes=0
for rest in itertools.product(alphabet,repeat=5):
 ls=[(0,1,2),*rest];w,n=witness(ls);count+=1;maxnodes=max(maxnodes,n)
 if w is None:raise AssertionError(ls)
rng=random.Random(174);samples=[]
for j in range(1000):
 ls=[rng.choice(alphabet) for _ in range(80)];w,n=witness(ls);maxnodes=max(maxnodes,n)
 if w is None:samples.append({'lists':ls,'failure':True})
 elif j<3:samples.append({'lists':ls,'word':w})
d=dict(exhaustive_length=6,alphabet_size=5,list_size=3,first_list_fixed=[0,1,2],assignments=count,meaning='All assignments up to global alphabet permutation; all shorter assignments extend to length 6.',random_seed=174,random_length=80,random_assignments=1000,failures=sum(x.get('failure',False) for x in samples),samples=samples,max_dfs_nodes=maxnodes,seconds=time.monotonic()-t)
(L/'outputs/square-lists.json').write_text(json.dumps(d,indent=2));print({k:v for k,v in d.items() if k!='samples'})
