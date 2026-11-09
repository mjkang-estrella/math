import pathlib,json,random,time,math
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(239);t=time.monotonic();n=7;k=3
V=[(i,j) for i in range(n) for j in range(n) if i!=j];N=len(V)
E=[(u,v) for u in range(N) for v in range(u+1,N) if V[u][0]==V[v][0] or V[u]==V[v][::-1]];m=len(E);inc=[[e for e,(a,b) in enumerate(E) if v in (a,b)] for v in range(N)]
assert N==42 and m==126
# 7 K6 cliques: 105 internal edges; 21 matching edges.
def cross(e,f,pos):
 a,b=E[e];c,d=E[f]
 if len({a,b,c,d})<4:return False
 a,b=sorted((pos[a],pos[b]));c,d=sorted((pos[c],pos[d]));return a<c<b<d or c<a<d<b
best=10**9;steps=0;restarts=0;history=[]
while time.monotonic()-t<100:
 order=list(range(N))
 # Start with clique blocks and a few interleavings; allow unrestricted subsequent swaps.
 for _ in range(restarts%12):
  a,b=rng.sample(range(N),2);order[a],order[b]=order[b],order[a]
 pos=[0]*N
 for i,v in enumerate(order):pos[v]=i
 page=[rng.randrange(k) for _ in E]
 pairs=[(e,f) for e in range(m) for f in range(e+1,m) if cross(e,f,pos)]
 adj=[set() for _ in E]
 for e,f in pairs:adj[e].add(f);adj[f].add(e)
 score=sum(page[e]==page[f] for e,f in pairs)
 for step in range(12000):
  if time.monotonic()-t>100:break
  temp=.12+1.8*(1-(step%3000)/3000)
  if rng.random()<.8:
   e=rng.randrange(m);old=page[e];new=(old+rng.randrange(1,k))%k
   delta=sum((page[f]==new)-(page[f]==old) for f in adj[e])
   if delta<=0 or rng.random()<math.exp(-delta/temp):page[e]=new;score+=delta
  else:
   i=rng.randrange(N-1);j=i+1
   if rng.random()<.05:j=rng.randrange(N)
   u,v=order[i],order[j]
   if u==v:continue
   affected=set(inc[u]+inc[v]); ps={(min(e,f),max(e,f)) for e in affected for f in range(m) if e!=f} if abs(i-j)>1 else {(min(e,f),max(e,f)) for e in inc[u] for f in inc[v] if e!=f}
   before={q for q in ps if cross(*q,pos)};pos[u],pos[v]=pos[v],pos[u];after={q for q in ps if cross(*q,pos)}
   delta=sum(page[e]==page[f] for e,f in after-before)-sum(page[e]==page[f] for e,f in before-after)
   if delta<=0 or rng.random()<math.exp(-delta/temp):
    order[i],order[j]=order[j],order[i];score+=delta
    for e,f in before-after:adj[e].remove(f);adj[f].remove(e)
    for e,f in after-before:adj[e].add(f);adj[f].add(e)
   else:pos[u],pos[v]=pos[v],pos[u]
  steps+=1
  if score<best:
   best=score;history.append({'step':steps,'seconds':time.monotonic()-t,'score':score});packet={'n':n,'pages':k,'vertices':V,'edges':E,'order':order[:],'page':page[:],'same_page_crossings':score};(D/'book-best.json').write_text(json.dumps(packet,indent=2)+'\n')
   print('best',best,'steps',steps,flush=True)
   if best==0:break
 if best==0:break
 restarts+=1
p=json.loads((D/'book-best.json').read_text());pos=[0]*N
for i,v in enumerate(p['order']):pos[v]=i
assert sum(cross(e,f,pos) and p['page'][e]==p['page'][f] for e in range(m) for f in range(e+1,m))==best
(D/'book-search.json').write_text(json.dumps({'seed':239,'n':n,'pages':k,'steps':steps,'restarts':restarts,'best_same_page_crossings':best,'seconds':time.monotonic()-t,'history':history,'claim':'Heuristic diagnostic; nonzero residual proves no lower bound.'},indent=2)+'\n')
