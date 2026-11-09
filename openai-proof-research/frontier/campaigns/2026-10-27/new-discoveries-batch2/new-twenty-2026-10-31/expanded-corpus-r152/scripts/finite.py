import sys;sys.path.insert(0,'/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/fresh-corpus-r10/pydeps')
import networkx as nx,itertools,json,pathlib,math
L=pathlib.Path(__file__).resolve().parents[1];out=[]
def eig(a):
 n=len(a)
 for _ in range(100*n*n):
  p,q=max(((i,j) for i in range(n) for j in range(i+1,n)),key=lambda ij:abs(a[ij[0]][ij[1]]))
  if abs(a[p][q])<1e-11:break
  theta=.5*math.atan2(2*a[p][q],a[q][q]-a[p][p]);c=math.cos(theta);s=math.sin(theta);ap=a[p][p];aq=a[q][q];v=a[p][q]
  a[p][p]=c*c*ap-2*s*c*v+s*s*aq;a[q][q]=s*s*ap+2*s*c*v+c*c*aq;a[p][q]=a[q][p]=0
  for i in range(n):
   if i not in (p,q):x=a[i][p];y=a[i][q];a[i][p]=a[p][i]=c*x-s*y;a[i][q]=a[q][i]=s*x+c*y
 return max(a[i][i] for i in range(n))-min(a[i][i] for i in range(n))
def spread(G,alpha):
 n=len(G);return eig([[alpha*G.degree(i) if i==j else (1-alpha)*G.has_edge(i,j) for j in range(n)] for i in range(n)])
counts={};spect=[]
for G in nx.graph_atlas_g():
 n=len(G);m=G.number_of_edges()
 if n<2 or n>6 or not nx.is_connected(G):continue
 edges=list(G.edges());valid=[]
 for mask in range(1,1<<m):
  deg=[0]*n
  for j,(a,b) in enumerate(edges):
   if mask>>j&1:deg[a]+=1;deg[b]+=1
  if all(deg[a]!=deg[b] for j,(a,b) in enumerate(edges) if mask>>j&1):valid.append(mask)
 dp=[100]*(1<<m);dp[0]=0;bybit=[[s for s in valid if s>>j&1] for j in range(m)]
 for mask in range(1,1<<m):
  j=(mask&-mask).bit_length()-1
  dp[mask]=min([1+dp[mask^s] for s in bybit[j] if s&mask==s]+[100])
 k=dp[-1];counts[(n,k)]=counts.get((n,k),0)+1
 if 4<k<100:out.append(dict(n=n,edges=edges,chromatic_index=k))
 if n>=5:
  kite=nx.complete_graph(n-1);kite.add_edge(n-2,n-1)
  for num in range(10,20):
   a=num/20;diff=spread(G,a)-spread(kite,a);spect.append(dict(n=n,m=m,alpha=a,difference=diff,violation=diff>1e-7))
(L/'outputs/local-irregular.json').write_text(json.dumps(dict(counts={str(k):v for k,v in counts.items()},violations=out),indent=2));(L/'outputs/spectral.json').write_text(json.dumps(spect,indent=2));print('local',counts,'violations',len(out));print('spectral cases',len(spect),'violations',sum(r['violation'] for r in spect),'max difference',max(r['difference'] for r in spect))
