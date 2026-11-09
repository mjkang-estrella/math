import sys,json,time
m=int(sys.argv[1]);E=[]
for i in range(m):
 for j in [1,2,3]:E.append((4*i,4*i+j))
 E.append((4*i+1,4*((i+1)%m)+1))
 if i<m-1:E.extend([(4*i+2,4*(i+1)+2),(4*i+3,4*(i+1)+3)])
 else:E.extend([(4*i+2,3),(4*i+3,2)])
inc=[[] for _ in range(4*m)]
for j,(u,v) in enumerate(E):inc[u].append(j);inc[v].append(j)
nodes=0;complete=0;start=time.time();answer=None

def paircheck(c):
 for a in range(1,8):
  for b in range(a+1,8):
   A={u for j,e in enumerate(E) if c[j]==a for u in e};B={u for j,e in enumerate(E) if c[j]==b for u in e}
   if A&B:continue
   if any((u in A and v in B) or (v in A and u in B) for u,v in E):continue
   return [a,b]

def dfs(c):
 global nodes,complete,answer
 nodes+=1
 if nodes>200000:return False
 while True:
  change=False
  for es in inc:
   missing=[e for e in es if c[e]==0]
   x=0
   for e in es:x^=c[e]
   if not missing and x:return False
   if len(missing)==1:
    if x==0:return False
    c[missing[0]]=x;change=True
  if not change:break
 if all(c):
  complete+=1;p=paircheck(c)
  if p:answer={'flow':c,'pair':p};return True
  return False
 best=min((es for es in inc if any(c[e]==0 for e in es)),key=lambda es:sum(c[e]==0 for e in es))
 j=next(e for e in best if c[e]==0)
 for v in range(1,8):
  d=c.copy();d[j]=v
  if dfs(d):return True
 return False
c=[0]*len(E)
for e,v in zip(inc[0],[1,2,3]):c[e]=v
dfs(c)
print(json.dumps({'flower_parameter':m,'order':4*m,'edges':E,'search_nodes':nodes,'complete_flows_examined':complete,'answer':answer,'seconds':time.time()-start}))
