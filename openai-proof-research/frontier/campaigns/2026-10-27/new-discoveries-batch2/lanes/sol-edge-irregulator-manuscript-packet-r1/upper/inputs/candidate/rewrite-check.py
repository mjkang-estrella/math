from pathlib import Path
p=Path(__file__).with_name('check.py');s=p.read_text().replace('import networkx as nx,itertools,json,pathlib,sys','import itertools,json,pathlib,sys')
a=s.index('for g in nx.graph_atlas_g():');z=s.index(' full=m',a)
s=s[:a]+'''def graphs():
 for n in range(2,7):
  pairs=list(itertools.combinations(range(n),2));lo,hi=(0,1<<len(pairs))
  if n==6:
   shard=int(sys.argv[1]);lo=shard*8192;hi=lo+8192
  elif int(sys.argv[1])!=0:continue
  for mask in range(lo,hi):
   edges=[e for i,e in enumerate(pairs) if mask>>i&1]
   seen={0}
   for _ in range(n):
    for u,v in edges:
     if u in seen or v in seen:seen.update((u,v))
   if len(seen)==n:yield n,edges
for n,edges in graphs():
 m=len(edges);opts=[m]*n;bridge=[m+1]*n
'''+s[z:]
s=s.replace("b/'checks.json'","b/('checks-'+sys.argv[1]+'.json')")
p.write_text(s)
