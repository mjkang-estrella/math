import itertools,math,random,json,pathlib
L=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(153);out=[]
# Exact s=1 intersecting families on six vertices, one choice per complementary triple pair.
E=[sum(1<<v for v in e) for e in itertools.combinations(range(6),3)];pairs=[(e,63^e) for e in E if e<(63^e)];qual=0;best=0
for choice in itertools.product(range(3),repeat=10):
 es=[p[c-1] for p,c in zip(pairs,choice) if c];common=63
 for e in es:common&=e
 if es and not common:qual+=1;best=max(best,len(es))
out.append({'n':6,'k':3,'s':1,'exhaustive_intersecting_families':3**10,'tau_gt_s':qual,'maximum':best,'bound':10})
for n in range(9,14):
 E=[sum(1<<v for v in e) for e in itertools.combinations(range(n),3)];best=0;eligible=0;w=[]
 for t in range(1000):
  rng.shuffle(E);es=[];unions=set()
  for e in E:
   if any(not (e&u) for u in unions):continue
   unions.update(e|f for f in es if not(e&f));es.append(e)
  if not unions:continue
  covers=any(all((e&((1<<i)|(1<<j))) for e in es) for i,j in itertools.combinations(range(n),2))
  if not covers:
   eligible+=1
   if len(es)>best:best=len(es);w=es[:]
 A=math.comb(5,2)*(n-5)+math.comb(5,3)
 HM=math.comb(n,3)-math.comb(n-2,3)-math.comb(n-5,2)+1
 out.append({'n':n,'k':3,'s':2,'random_seed':153,'saturated_greedy_trials':1000,'eligible_tau_gt_2':eligible,'maximum_found':best,'bound':max(A,HM,56),'witness_bitmasks':w})
 print(n,best,max(A,HM,56),flush=True)
(L/'outputs/hypermatch.json').write_text(json.dumps(out,indent=2))
