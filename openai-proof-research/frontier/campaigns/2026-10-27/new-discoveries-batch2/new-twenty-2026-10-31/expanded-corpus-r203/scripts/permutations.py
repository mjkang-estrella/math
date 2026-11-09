import itertools,json,pathlib,sys
# Reuse only clique function, avoiding top-level search.
s=pathlib.Path(sys.argv[1]).read_text();exec(s[s.index('def clique'):s.index('for m in [7,8]:')])
for n in range(2,7):
 P=list(itertools.permutations(range(n)))
 for t in range(1,n+1):
  if n==6 and t<3:continue
  adj=[sum(1<<j for j,q in enumerate(P) if i!=j and sum(a==b for a,b in zip(p,q))>=t) for i,p in enumerate(P)]
  sizes=[sum(sum(p[i]==i for i in range(t+2*k))>=t+k for p in P) for k in range((n-t)//2+1)]
  c=clique(adj);assert len(c)<=max(sizes),(n,t,len(c),sizes)
  print(json.dumps({'n':n,'t':t,'permutations':len(P),'maximum_clique':len(c),'A_sizes':sizes,'scope':'maximum size only; equality classification unchecked'}),flush=True)
