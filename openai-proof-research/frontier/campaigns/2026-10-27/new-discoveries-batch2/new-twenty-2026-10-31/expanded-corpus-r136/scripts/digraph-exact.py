import pathlib,sys,itertools,json,collections,time
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'sources/vendor/networkx-networkx-3.4.2'));import networkx as nx
n=6;full=63
# A vertex of out-eccentricity >=3 has at most n-3 outgoing neighbors.
# W >= 2*n*(n-1)-m+n = 66-m; W<=50 forces m>=16.
# Thus some row has degree3. Relabel that vertex0 and its neighbors1,2,3.
options=[]
for i in range(6):
 options.append([(sum(1<<j for j in s),3-len(s)) for d in [3,2,1] for s in itertools.combinations([j for j in range(6) if j!=i],d)])
a=[14]+[0]*5;total=radius3=short=0;found=[];sig=collections.Counter()
base=nx.DiGraph();base.add_nodes_from(range(6))
for u in range(6):
 for v in range(6):
  if u!=v and (u//3==v//3 and v%3<=u%3+1 or u//3!=v//3 and v%3==0):base.add_edge(u,v)
def check():
 global total,radius3,short
 total+=1;W=0;eccs=[]
 for u in range(6):
  seen=(1<<u)|a[u];two=seen;bits=a[u]
  while bits:
   b=bits&-bits;bits-=b;two|=a[b.bit_length()-1]
  if two==full:return
  # Every row must miss something after two steps.
  dist=1;front=a[u];visited=1<<u;w=0
  while front:
   visited|=front;w+=dist*front.bit_count();nxt=0;bits=front
   while bits:
    b=bits&-bits;bits-=b;nxt|=a[b.bit_length()-1]
   front=nxt&~visited;dist+=1
  if visited!=full:return
  W+=w;eccs.append(dist-1)
  if W>50:return
 if min(eccs)!=3:return
 radius3+=1
 if W<=50:
  g=nx.DiGraph();g.add_nodes_from(range(6));g.add_edges_from((u,v) for u in range(6) for v in range(6) if a[u]>>v&1)
  iso=nx.is_isomorphic(g,base);sig[str((W,iso))]+=1
  if W<50 or not iso:
   found.append({'adj':a[:],'W':W,'ecc':eccs,'isomorphic_to_source':iso});print('CANDIDATE',found[-1],flush=True)
def rec(i,deficit):
 if i==6:check();return
 for mask,d in options[i]:
  if deficit+d<=2:a[i]=mask;rec(i+1,deficit+d)
rec(1,0)
out={'normalized_matrices_checked':total,'within_threshold_radius3':radius3,'outcomes':dict(sig),'candidates':found,'scope':'all six-vertex digraphs with outradius3 and W<=50, up to fixing one degree3 row and its neighbors; proof of bound in comments; exact isomorphism test uses NetworkX'}
(D/'outputs/digraph-exact.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
