import json,pathlib,itertools
L=pathlib.Path(__file__).resolve().parents[1];rows=json.loads((L/'outputs/delta-witness.json').read_text())
def chain(B):
 ends=[i for i,r in enumerate(B) if sorted(v for v in r if v)==[1,1,2,2]]
 middle=[i for i,r in enumerate(B) if sorted(v for v in r if v)==[1,1,1,1,2]]
 def dfs(path,used):
  i=path[-1]
  for j in ends+middle:
   if j in path or B[i][j]!=1:continue
   for k in range(len(B)):
    if k in (i,j) or B[i][k]!=1 or B[j][k]!=1:continue
    edges={tuple(sorted(e)) for e in [(i,j),(i,k),(j,k)]}
    if edges&used:continue
    if j in ends:return [(i,j,k)]
    c=dfs(path+[j],used|edges)
    if c:return [(i,j,k)]+c
  return None
 for i in ends:
  c=dfs([i],set())
  if c:return c
 return None
for r in rows:r['chain']=chain(r['matrix'])
(L/'outputs/delta-chains.json').write_text(json.dumps(rows,indent=2));print('states',len(rows),'chains',sum(bool(r['chain']) for r in rows),'lengths',sorted(set(len(r['chain']) for r in rows if r['chain'])))
