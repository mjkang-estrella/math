import pathlib,itertools,json,sys
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186')
def bisection(n):
 vals=list(range(1,1<<n));N=len(vals);adj=[0]*N
 for i,a in enumerate(vals):
  for j,b in enumerate(vals):
   k=2*(a&b).bit_count()
   if i!=j and (k==a.bit_count() or k==b.bit_count()):adj[i]|=1<<j
 best=[];nodes=0
 def expand(P,chosen):
  nonlocal best,nodes
  nodes+=1
  if not P:
   if len(chosen)>len(best):best=chosen[:]
   return
  order=[];bounds=[];left=P;color=0
  while left:
   color+=1;Q=left
   while Q:
    bit=Q&-Q;v=bit.bit_length()-1;order.append(v);bounds.append(color);left^=bit;Q^=bit;Q&=~adj[v]
  for v,c in zip(reversed(order),reversed(bounds)):
   if len(chosen)+c<=len(best):return
   expand(P&adj[v],chosen+[v]);P&=~(1<<v)
 expand((1<<N)-1,[])
 return {'n':n,'maximum_nonempty_family':len(best),'witness':[vals[v] for v in best],'nodes':nodes,'coverage':'all cliques of pair-compatibility graph, pruned by proper-colouring upper bound'}
if sys.argv[1]=='bisection':
 out=[]
 for n in range(1,9):
  r=bisection(n);out.append(r);print(json.dumps(r),flush=True)
 (L/'outputs/bisection.json').write_text(json.dumps(out,indent=2))
if sys.argv[1]=='permanent':
 out=[]
 for p in [2,3,5,7,11]:
  hist={};fail=[]
  for mask in range(1,1<<p):
   A=[x for x in range(p) if mask>>x&1];products={a*b%p for a in A for b in A};values={(a+b)%p for a in products for b in products};bound=min(len(A)**2,p)
   if len(values)<bound:fail.append({'A':A,'values':sorted(values),'bound':bound})
  out.append({'p':p,'subsets_tested':(1<<p)-1,'d':2,'failures':fail});print(p,'failures',len(fail),flush=True)
 (L/'outputs/permanent.json').write_text(json.dumps(out,indent=2))
