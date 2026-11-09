import sys,collections,json

def graph(g,k):
 start=(-1,-1);adj={};q=[start]
 for v in q:
  r,s=(0,0) if v==start else v;e=[]
  for b in range(g):
   a=(k*b+s)%g;u=(k*b+s)//g;t=b+r*g-k*a
   if 0<=u<k and 0<=t<k and (v!=start or a*b):
    w=(t,u);e.append(w)
    if w not in adj and w not in q:q.append(w)
  adj[v]=e
 keep={v for v in q if v!=start and (v[0]==v[1] or v[::-1] in adj[v])}
 while True:
  z=keep|{v for v in q if any(w in keep for w in adj[v])}
  if z==keep:break
  keep=z
 return {v:[w for w in adj[v] if w in keep] for v in q if v in keep}
def check(a,n):
 start=(-1,-1);zero=(0,0);cycle=set(a)-{start,zero}
 if len(cycle)!=2*n-1:return False
 if zero not in a or zero not in a[zero]:return False
 pred=[v for v in cycle if zero in a[v]];succ=[w for w in a[zero] if w!=zero]
 if len(pred)!=1 or len(succ)!=1 or a[start]!=succ:return False
 for v in cycle:
  if len([w for w in a[v] if w in cycle])!=1:return False
 v=next(iter(cycle));seen=set()
 while v not in seen:seen.add(v);v=next(w for w in a[v] if w in cycle)
 return len(seen)==len(cycle) and succ[0] in a[pred[0]]
stop=int(sys.argv[1]);ts=range(3,int(sys.argv[2])+1);count=0
for n in range(2,stop+1):
 for t in ts:
  g=(n*n+n)*t-n*n+n+1;k=n*n*t-(n-1)**2;a=graph(g,k);count+=1
  if not check(a,n):print('FAIL',n,t,g,k,a,flush=True);sys.exit(1)
 print('PASS n',n,'t',min(ts),max(ts),'largest g',g,'nodes',len(a),flush=True)
print('total',count)
