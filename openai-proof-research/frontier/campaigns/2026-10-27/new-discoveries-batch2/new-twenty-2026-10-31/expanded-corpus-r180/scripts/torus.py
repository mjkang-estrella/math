import pathlib,random,math,json
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(180382041);results=[]
for n,m in [(3,4),(3,5),(3,7),(4,5)]:
 V=n*m;edges=set()
 for i in range(n):
  for j in range(m):
   v=i*m+j
   edges.add(tuple(sorted((v,((i+1)%n)*m+j))));edges.add(tuple(sorted((v,i*m+(j+1)%m))))
 edges=sorted(edges);q=len(edges);target=4*V+2;best=10**9;answer=None;steps=0
 assert q==2*V
 for restart in range(20):
  labels=list(range(1,q+1));rng.shuffle(labels);weights=[0]*V
  for (u,v),l in zip(edges,labels):weights[u]+=l;weights[v]+=l
  score=sum((w-target)**2 for w in weights)
  for t in range(50000):
   a,b=rng.sample(range(q),2);delta=labels[b]-labels[a];change={}
   for v in edges[a]:change[v]=change.get(v,0)+delta
   for v in edges[b]:change[v]=change.get(v,0)-delta
   diff=sum(2*(weights[v]-target)*d+d*d for v,d in change.items());temp=12*(1-t/50000)**2+.2
   if diff<=0 or rng.random()<math.exp(max(-700,-diff/temp)):
    labels[a],labels[b]=labels[b],labels[a]
    for v,d in change.items():weights[v]+=d
    score+=diff
   steps+=1;best=min(best,score)
   if score==0:answer=labels[:];break
  if answer:break
 result={'n':n,'m':m,'proposals':steps,'best_squared_error':best,'certificate_labels':answer,'edge_order':edges,'target':target,'interpretation':'finite existence diagnostic only; failure to find would not refute conjecture'}
 if answer:
  assert sorted(answer)==list(range(1,q+1));assert all(sum(l for e,l in zip(edges,answer) if v in e)==target for v in range(V))
 results.append(result);print({k:v for k,v in result.items() if k not in ['certificate_labels','edge_order']},flush=True)
 (D/'outputs/torus.json').write_text(json.dumps(results,indent=2))
