import itertools,json,pathlib,time
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for m,n in [(3,3),(3,4),(3,5),(3,6),(4,4),(4,5)]:
 N=m*n;full=(1<<N)-1;adj=[]
 for i in range(N):
  x,y=divmod(i,n);adj.append(sum(1<<(a*n+b) for a,b in [(x-1,y),(x+1,y),(x,y-1),(x,y+1)] if 0<=a<m and 0<=b<n))
 mandatory=sum(1<<i for i,a in enumerate(adj) if a.bit_count()<3);free=[i for i in range(N) if not (mandatory>>i&1)]; counts={3:0,4:0}; minima={}; witnesses={}
 def closure(s,q):
  while True:
   z=s
   for i,a in enumerate(adj):
    if s>>i&1 or (a&s).bit_count()<3:continue
    if q==4 or any((a&s)>>j&1 and (adj[j]&~s).bit_count()<=q for j in range(N)):z|=1<<i
   if z==s:return s==full
   s=z
 for k in range(len(free)+1):
  for comb in itertools.combinations(free,k):
   s=mandatory|sum(1<<i for i in comb)
   for q in [4,3]:
    if q in minima:continue
    counts[q]+=1
    if closure(s,q):minima[q]=k+mandatory.bit_count();witnesses[q]=s
  if len(minima)==2:break
 r={'grid':[m,n],'minima':minima,'tested':counts,'witness_masks':witnesses,'coverage':'all seed subsets containing mandatory degree<3 vertices through first successful size for each q; remainder of final size skipped for q after success'};out.append(r);print(r,flush=True)
(D/'outputs/grids.json').write_text(json.dumps(out,indent=2)+'\n')
