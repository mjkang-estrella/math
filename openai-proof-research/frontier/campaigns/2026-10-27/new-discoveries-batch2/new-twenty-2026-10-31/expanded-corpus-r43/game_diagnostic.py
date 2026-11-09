import resource,random,itertools,json,time
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
rng=random.Random(350625);start=time.monotonic()
def play(edges,t,order,prefix=None):
 t=list(t);score=0;seq=[]
 for j,v in enumerate(order):
  w=max([max(0,1-sum(t[x] for x in e)) for e in edges if v in e] or [0])
  if prefix is not None and j==0:w*=prefix
  t[v]+=w;score+=w;seq.append((v,w))
 return score,seq
for trial in range(300):
 n=5;edges=[s for k in [2,3] for s in itertools.combinations(range(n),k) if rng.random()<.3]
 if not edges:continue
 # t>.4 ensures any legal total in n5 graph <=1 (each coordinate can add <=.2).
 t=[rng.randint(42,49)/100 for _ in range(n)]
 orders=list(itertools.permutations(range(n)));g=max((play(edges,t,o) for o in orders),key=lambda a:a[0]);best=g
 for o in orders:
  for f in [.25,.5,.75]:
   p=play(edges,t,o,f)
   if p[0]>best[0]+1e-9:best=p
 if best[0]>g[0]+1e-8:
  print(json.dumps({'trial':trial,'edges':edges,'t':t,'greedy':g,'fractional':best}),flush=True);break
else:print('No gap in 300 seeded random graph/hypergraph states; only one fractional prefix then greedy suffix tested.')
print('elapsed',time.monotonic()-start)
