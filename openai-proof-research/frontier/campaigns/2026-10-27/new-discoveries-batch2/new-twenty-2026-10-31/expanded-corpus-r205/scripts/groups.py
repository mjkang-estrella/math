import itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
def test(perms,label):
 n=len(perms);idx={x:i for i,x in enumerate(perms)};d=len(perms[0]);table=[[idx[tuple(p[q[j]] for j in range(d))] for q in perms] for p in perms];e=idx[tuple(range(d))]
 def extend(H,x):
  H=set(H);H.add(x)
  while True:
   K={table[a][b] for a in H for b in H}
   if K<=H:return frozenset(H)
   H|=K
 subs={frozenset([e])};queue=list(subs)
 for H in queue:
  for x in range(n):
   if x in H:continue
   K=extend(H,x)
   if K not in subs:subs.add(K);queue.append(K)
 proper=[H for H in subs if len(H)<n];maxs=[H for H in proper if not any(H<K for K in proper)]
 sig=[tuple(x in H for H in maxs) for x in range(n)]
 gen=[[len(extend([x],y))==n for y in range(n)] for x in range(n)]
 spread=all(any(gen[x][y] for y in range(n) if x!=y) for x in range(n) if x!=e)
 bad=[(x,y) for x in range(n) for y in range(x) if gen[x]==gen[y] and sig[x]!=sig[y]]
 r={'label':label,'order':n,'subgroups':len(subs),'maximal_subgroups':len(maxs),'nonzero_spread':spread,'equivalence_mismatches':bad};print(json.dumps(r),flush=True);return r
out=[]
for d in range(3,6):
 p=list(itertools.permutations(range(d)));out.append(test(p,'S'+str(d)));out.append(test([x for x in p if sum(x[i]>x[j] for i in range(d) for j in range(i+1,d))%2==0],'A'+str(d)))
for d in range(3,16):out.append(test(list(dict.fromkeys(tuple((s*i+a)%d for i in range(d)) for s in [1,-1] for a in range(d))),'D'+str(2*d)))
(D/'outputs/groups.json').write_text(json.dumps(out,indent=2))
