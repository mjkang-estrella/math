import pathlib,json,collections
L=pathlib.Path(__file__).resolve().parents[1];M=json.loads((L/'evidence/math.json').read_text());F=list(map(set,M['facets']))
C={}
for m in range(3):
 adj={i:{j for j,g in enumerate(F) if i!=j and len(f&g)>=m+1} for i,f in enumerate(F)};unseen=set(adj);parts=[]
 while unseen:
  reached={min(unseen)}
  while True:
   nxt=reached|set().union(*(adj[i] for i in reached))
   if nxt==reached:break
   reached=nxt
  parts.append(sorted(reached));unseen-=reached
 C[m]=parts
(L/'evidence/connectivity.json').write_text(json.dumps(C,indent=2)+'\n');print(C)
P=L.parent/'expanded-corpus-r212/sources'
with (L/'evidence/SOURCE-QUOTES.md').open('a') as o:
 for v,rs in [('v1',[(411,418)]),('v2',[(141,158),(238,244)]),('v3',[(135,149),(274,288)])]:
  name='2508.17854'+('' if v=='v3' else v)+'.txt';a=(P/name).read_text().split('\n');o.write('\n# Supplement '+v+'\n\n')
  for x,y in rs:o.write('```text\n'+''.join(f'{i}: {a[i-1]}\n' for i in range(x,y+1))+'```\n')
