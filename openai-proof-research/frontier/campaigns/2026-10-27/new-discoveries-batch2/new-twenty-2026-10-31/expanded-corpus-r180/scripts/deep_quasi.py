import pathlib,runpy,random,math,json,time
D=pathlib.Path(__file__).resolve().parents[1]
# No implicit script directory: load an explicit real path.
ns={'__name__':'loaded'}
src=(D/'scripts/finite.py').read_text().split("if sys.argv[1]")[0]
exec(compile(src,str(D/'scripts/finite.py'),'exec'),{'__file__':str(D/'scripts/finite.py'),**ns},ns)
# Independent scoring implementation, making the maximum vertex surplus as small as possible.
rng=random.Random(180381984)
def margins(a,n):
 ins=[sum(1<<u for u in range(n) if a[u]>>v&1) for v in range(n)]
 return [x.bit_count()-sum(1 for v in range(n) if not((x|1<<u)>>v&1) and ins[v] and not ins[v]&~(x|1<<u)) for u,x in enumerate(a) if x]
results=[]
for n in [6,8,10,12,16]:
 best=n; best_a=None;steps=0
 for restart in range(20):
  a=[1<<rng.choice([v for v in range(n) if v!=u]) for u in range(n)]
  ms=margins(a,n);score=max(ms)+sum(max(0,m) for m in ms)/(n*n)
  for t in range(2000):
   u=rng.randrange(n);v=rng.choice([v for v in range(n) if v!=u]);a[u]^=1<<v
   ms=margins(a,n);new=max(ms) + sum(max(0,m) for m in ms)/(n*n) if ms else n
   temp=.15*(1-t/2000)+.001
   if new<=score or rng.random()<math.exp(min(0,(score-new)/temp)):score=new
   else:a[u]^=1<<v
   steps+=1
   if ms and max(ms)<best:best=max(ms);best_a=a[:]
   if best<0:print('COUNTEREXAMPLE',n,best_a,flush=True);raise SystemExit
 r={'n':n,'proposals':steps,'best_max_surplus':best,'best_adjacency_masks':best_a};results.append(r);print(r,flush=True)
 (D/'outputs/deep-quasi.json').write_text(json.dumps(results,indent=2))
