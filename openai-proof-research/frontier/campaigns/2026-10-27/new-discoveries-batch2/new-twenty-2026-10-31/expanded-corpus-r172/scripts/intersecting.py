import itertools,math,time,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];n=8;k=3
sets=[sum(1<<v for v in a) for a in itertools.combinations(range(n),k)];N=len(sets)
adj=[sum(1<<j for j,b in enumerate(sets) if i!=j and a&b) for i,a in enumerate(sets)]
start=time.monotonic();count=0;viol=[];checks=0;timed=False;maxsize=0
ps=[1,2,3,4,8];base=[math.comb(n-1,k-1)]+[math.comb(n-2,k-2)]*(n-1)
bounds={p:sum(d**p for d in base) for p in ps};L=base[1];inputbound=base[0]-L
hist={}
def bk(R,P,X):
 global count,checks,timed,maxsize
 if timed:return
 if not P and not X:
  count+=1;degrees=[sum(1 for i in R if sets[i]>>v&1) for v in range(n)];maxsize=max(maxsize,len(R));hist[len(R)]=hist.get(len(R),0)+1
  for p in ps:
   checks+=1;val=sum(d**p for d in degrees)
   if val>bounds[p]:viol.append({'family':[sets[i] for i in R],'p':p,'lhs':val,'rhs':bounds[p]})
  if sum(max(0,d-L) for d in degrees)>inputbound:viol.append({'positive_part_only':degrees})
  if count%1000==0 and time.monotonic()-start>95:timed=True
  return
 union=P|X
 if union:
  vs=[]
  while union:
   b=union&-union;union-=b;u=b.bit_length()-1;vs.append(u)
  u=max(vs,key=lambda u:(P&adj[u]).bit_count());cand=P&~adj[u]
 else:cand=P
 while cand:
  b=cand&-cand;cand-=b;v=b.bit_length()-1
  bk(R+[v],P&adj[v],X&adj[v]);P-=b;X|=b
bk([], (1<<N)-1,0)
r={'n':n,'k':k,'r':1,'method':'Bron-Kerbosch with pivot over pairwise-intersecting k-sets; every inclusion-maximal family if completed','maximal_families':count,'complete':not timed,'exact_p':ps,'max_size':maxsize,'size_histogram':hist,'violations':viol,'seconds':time.monotonic()-start,'limitation':'p-grid alone does not imply all real p; monotonicity reduces fixed-p extremum to maximal families.'}
(D/'outputs/intersecting-search.json').write_text(json.dumps(r,indent=2));print(r)
