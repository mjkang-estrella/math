import json,pathlib,resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(20,25));signal.alarm(30)
L=pathlib.Path(__file__).parent;rows=[]
for a in range(1,11):
 for b in range(1,a+1):
  for e in range(2):
   if e and (a%2 or b%2):continue
   V=[(u,v) for u in range(a+1) for v in range(e,e+b+1) if (u-v)%2==0]
   S=[(u,v) for u in range(a-5,6) for v in range(e+b-5,e+6) if (u-v)%2==0]
   cs=[frozenset(i for i,(x,y) in enumerate(V) if (abs(x-u)==4 and y==v) or (x==u and abs(y-v)==4)) for u,v in S]
   cs += [frozenset(i for i,(u,v) in enumerate(V) if [u==0,u==a,v==e,v==e+b][side]) for side in range(4)]
   unique=set(cs);G=sorted([sorted(c) for c in unique if not any(d<c for d in unique)])
   adj=[[j for j,(x,y) in enumerate(V) if abs(u-x)==abs(v-y)==1] for u,v in V]
   rows.append(dict(a=a,b=b,e=e,V=V,S=S,G=G,adj=adj))
(L/'group-domains.json').write_text(json.dumps(rows,separators=(',',':'))+'\n')
print(len(rows),'domains',sum(bool(r['G'][0]) for r in rows),'nonempty')
