import sys,pathlib,json,itertools,hashlib
from complex import cm,fv,balanced,D
vendor=D.parent/'expanded-corpus-r65/vendor';sys.path.insert(0,str(vendor))
import networkx as nx
allvec={};witness={};missing=[];counts={}
for G in nx.graph_atlas_g():
 n=len(G)
 if not n:continue
 E={1<<a|1<<b for a,b in G.edges()};K={x for x in range(1<<n) if all((1<<a|1<<b) in E for a,b in itertools.combinations([i for i in range(n) if x>>i&1],2))}
 counts.setdefault(n,dict(graphs=0,CM=0,balancedCM=0));counts[n]['graphs']+=1
 if not cm(K):continue
 counts[n]['CM']+=1;v=fv(K);allvec[(n,v)]=nx.to_graph6_bytes(G,header=False).decode().strip()
 if balanced(K,n):witness[n,v]=nx.to_graph6_bytes(G,header=False).decode().strip();counts[n]['balancedCM']+=1
for (n,v),g in allvec.items():
 if (n,v) not in witness:missing.append(dict(n=n,f_vector=v,graph6=g))
o=dict(method='all isomorphism classes in NetworkX graph atlas through seven vertices; Reisner CM over F2; balanced flag witnesses on same vertices',counts=counts,distinct_CM_vectors=len(allvec),missing_balanced_flag_witness=missing,witnesses=[dict(n=n,f_vector=v,graph6=g) for (n,v),g in sorted(witness.items())],vendor=str(vendor),limitation='Unmatched vectors do not refute conjecture: general balanced CM complexes need not be flag.')
(D/'outputs/340460-atlas-search.json').write_text(json.dumps(o,indent=2)+'\n');print(counts,'vectors',len(allvec),'missing',missing)
