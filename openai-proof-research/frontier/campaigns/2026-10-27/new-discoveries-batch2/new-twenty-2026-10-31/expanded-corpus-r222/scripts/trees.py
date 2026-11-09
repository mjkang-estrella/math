import pathlib,types,json,sys
D=pathlib.Path(__file__).resolve().parents[1]
# Reuse locally authored exact checker, without running its enumeration driver.
s=(D/'scripts/isolation.py').read_text().split('rng=random.Random(222)')[0];scope={'__file__':str(D/'scripts/isolation.py')};exec(compile(s,str(D/'scripts/isolation.py'),'exec'),scope);check=scope['check']
def canon(n,E):
 a=[[] for _ in range(n)]
 for i,j in E:a[i].append(j);a[j].append(i)
 def enc(v,p):return '('+''.join(sorted(enc(w,v) for w in a[v] if w!=p))+')'
 return min(enc(v,-1) for v in range(n))
trees={'(())':[(0,1)]}
for n in range(3,int(sys.argv[1])+1):
 nxt={}
 for E in trees.values():
  for i in range(n-1):
   F=E+[(i,n-1)];key=canon(n,F)
   if key not in nxt:nxt[key]=F
 trees=nxt;hist={};mx=[0,0]
 for E in trees.values():
  q=check(n,E);hist[str(q)]=hist.get(str(q),0)+1;mx=[max(mx[i],q[i]) for i in [0,1]]
  if max(q)>(3*n+6)//7:print('VIOLATION',n,E,q,flush=True);sys.exit()
 print(json.dumps({'vertices':n,'unlabeled_trees':len(trees),'max':mx,'histogram':hist}),flush=True)
