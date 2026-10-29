import json,os,collections,resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(60,65));signal.alarm(70)
L=os.path.dirname(__file__)
rows=[]
for a in range(1,11):
 for b in range(1,a+1):
  for e in range(2):
   V={(u,v) for u in range(a+1) for v in range(e,e+b+1) if (u-v)%2==0}
   S={(u,v) for u in range(a-5,6) for v in range(e+b-5,e+6) if (u-v)%2==0}
   con=[{(u+du,v+dv) for du,dv in [(4,0),(-4,0),(0,4),(0,-4)]}&V for u,v in S]
   con += [{(u,v) for u,v in V if u==0},{(u,v) for u,v in V if u==a},{(u,v) for u,v in V if v==e},{(u,v) for u,v in V if v==e+b}]
   # Minimal transversals with a cheap exact bounding-box tree lower bound.
   unique=set(map(frozenset,con));cons=[c for c in unique if not any(d<c for d in unique)]
   row={'a':a,'b':b,'e':e,'cells':len(V),'centers':len(S),'constraints':len(cons)}
   if any(not c for c in cons):row['status']='empty-constraint'
   else:row['status']='residual'
   rows.append(row)
open(L+'/domains.json','w').write(json.dumps(rows,indent=2)+'\n')
print(collections.Counter(r['status'] for r in rows));print([r for r in rows if r['status']=='residual'])
