import itertools,pathlib,json,collections
D=pathlib.Path(__file__).resolve().parents[1];out={}
for n,values in [(2,range(-2,3)),(3,range(3))]:
 perms=list(itertools.permutations(range(n)));counts=collections.Counter();fails=[];maxit=0
 for flat in itertools.product(values,repeat=n*n):
  W=[flat[i*n:(i+1)*n] for i in range(n)];scores=[sum(W[i][p[i]] for i in range(n)) for p in perms];best=max(scores)
  if scores.count(best)!=1:counts['nonunique_skipped']+=1;continue
  counts['unique']+=1;p=[0]*n;seen=set();done=False
  for t in range(1,301):
   bids=[[W[i][j]-max(W[i][l]-p[l] for l in range(n) if l!=j) for j in range(n)] for i in range(n)];winners=[max(range(n),key=lambda i:bids[i][j]) for j in range(n)];p=[max(bids[i][j] for i in range(n)) for j in range(n)]
   if len(set(winners))==n:done=True;maxit=max(maxit,t);break
   # Translation of all prices is irrelevant; normalized-state recurrence is an exact cycle diagnostic.
   key=tuple(x-min(p) for x in p)
   if key in seen:counts['repeated_price_difference']+=1;break
   seen.add(key)
  if not done:fails.append(dict(weights=W,iterations=t,prices=p))
 out[n]=dict(counts=dict(counts),max_termination_iteration=maxit,nonterminations_or_capped=fails,tie_policy='smallest buyer index per object; other tie policies untested',cap=300)
(D/'outputs/auction.json').write_text(json.dumps(out,indent=2));print(out)
