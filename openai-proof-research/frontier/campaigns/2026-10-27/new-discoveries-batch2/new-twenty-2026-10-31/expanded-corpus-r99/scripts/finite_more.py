import os,resource,time,itertools,json,sys
resource.setrlimit(resource.RLIMIT_CPU,(110,110));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);start=time.time();mode=sys.argv[1];out={'coverage':[],'counterexamples':[]}
if mode=='facial':
 import networkx as nx
 for G in nx.graph_atlas_g():
  n=len(G)
  if n<2 or not nx.is_connected(G):continue
  yes,emb=nx.check_planarity(G)
  if not yes:continue
  E=[tuple(sorted(e))for e in G.edges()];idx={e:i for i,e in enumerate(E)};seen=set();faces=[]
  for a,b in emb.edges():
   if (a,b)not in seen:
    vs=emb.traverse_face(a,b,seen);faces.append([idx[tuple(sorted((vs[i],vs[(i+1)%len(vs)])))]for i in range(len(vs))])
  for ell in range(4,13):
   H=nx.Graph();H.add_nodes_from(range(len(E)))
   for F in faces:
    for i in range(len(F)):
     for d in range(1,min(ell+1,len(F))):
      if F[i]!=F[(i+d)%len(F)]:H.add_edge(F[i],F[(i+d)%len(F)])
   C=nx.coloring.greedy_color(H,strategy='saturation_largest_first');num=max(C.values(),default=-1)+1
   out['coverage'].append({'graph6':nx.to_graph6_bytes(G,header=False).decode().strip(),'ell':ell,'colors':num,'bound':3*ell+1,'embedding':'one networkx planar embedding'})
   if num>3*ell+1:out['counterexamples'].append({'status':'greedy_alarm_only','entry':out['coverage'][-1]})
elif mode=='pdg':
 from fractions import Fraction as F
 from math import prod as mathprod, factorial as mathfactorial
 for k in [3,4,5,6]:
  n=k+1;E=list(itertools.combinations(range(n),k));count=free=0;best=F(0);bestentry=None
  # weighted blow-ups: all types on k+1 vertices, grid barycentre and all two-class weight vectors
  weights=[[F(1,n)]*n]
  for mask in range(1,(1<<n)-1):
   a=mask.bit_count()
   for den in [k,2*k]:
    for b in range(1,den):weights.append([F(b,den*a)if mask>>v&1 else F(den-b,den*(n-a))for v in range(n)])
  # cap k>=5 to deterministic sample of state words; full k3,4
  seq=itertools.product(range(k+2),repeat=n)
  if k>=5:seq=itertools.islice(seq,20000)
  for C in seq:
   count+=1;bad=False
   for I in itertools.combinations(range(n),3):
    if all(C[i]for i in I):
     core=set.intersection(*(set(E[i])for i in I))
     if any(C[i]>=2 and E[i][C[i]-2]not in core for i in I):bad=True;break
   if bad:continue
   free+=1
   theta=F(k,k-1)**(k-1)
   for x in weights:
    val=sum((F(1)if C[i]==1 else theta)*mathprod(x[v]for v in E[i])for i in range(n)if C[i])*mathfactorial(k)
    if val>best:best=val;bestentry={'types':C,'weights':list(map(str,x))}
   if time.time()-start>100:break
  out['coverage'].append({'k':k,'template_vertices':n,'state_words':count,'free':free,'best_blowup_density':str(best),'best':bestentry,'complete_state_enumeration':count==(k+2)**n})
  json.dump(out,open('outputs/'+mode+'.json','w'),indent=2)
  if time.time()-start>100:break
out['seconds']=time.time()-start;json.dump(out,open('outputs/'+mode+'.json','w'),indent=2);print('coverage',len(out['coverage']),'seconds',out['seconds'])
