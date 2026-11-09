import os,resource,time,itertools,json,random
resource.setrlimit(resource.RLIMIT_CPU,(110,110));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);import networkx as nx
out={'k2_exhaustive':[],'k3_search':[]};start=time.time()
for G in nx.graph_atlas_g():
 n=len(G)
 if n<2:continue
 E=list(G.edges());p=list(range(len(E)))
 def root(a):
  while p[a]!=a:a=p[a]
  return a
 for i,a in enumerate(E):
  for j,b in enumerate(E[:i]):
   if not set(a)&set(b):p[root(i)]=root(j)
 cd=[len({root(i)for i,e in enumerate(E)if v in e})for v in range(n)]
 if sum(cd)>=3*n:out['k2_exhaustive'].append({'n':n,'edges':E,'sum_color_degree':sum(cd),'exception_K4':n==4 and len(E)==6})
# 7 vertices k3; local colour search, nonedge allowed, objective color degree with rainbow penalty
rng=random.Random(350763);n=7;E=list(itertools.combinations(range(n),2));triples=[I for I in itertools.combinations(range(len(E)),3)if len(set(sum((list(E[i])for i in I),[])))==6]
def obj(C):
 cd=sum(len({C[i]for i,e in enumerate(E)if v in e and C[i]>=0})for v in range(n));bad=sum(len({C[i]for i in I})==3 and min(C[i]for i in I)>=0 for I in triples);return cd-5*bad,cd,bad
best=(0,0,0);bestC=None;count=0
while time.time()-start<100:
 C=[rng.randrange(-1,7)for _ in E];score=obj(C)
 for k in range(1000):
  i=rng.randrange(len(E));old=C[i];C[i]=rng.randrange(-1,7);new=obj(C);temp=max(.05,1-k/1000)
  import math
  if new[0]>=score[0] or rng.random()<math.exp((new[0]-score[0])/temp):score=new
  else:C[i]=old
  count+=1
  if score[2]==0 and score[1]>best[1]:best=score;bestC=C[:]
 out['k3_search']={'n':7,'proposals':count,'best':best,'edge_colors':bestC,'threshold_sum':35,'seconds':time.time()-start};json.dump(out,open('outputs/rainbow.json','w'),indent=2)
print(out)
