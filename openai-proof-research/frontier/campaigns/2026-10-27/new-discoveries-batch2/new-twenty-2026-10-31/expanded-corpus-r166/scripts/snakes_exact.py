import pathlib,sys,json
D=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166')
s=(D/'scripts/snakes.py').read_text().split('# Exact common independent set')[0]
exec(compile(s,'snakes.py','exec'))
E=sorted(set((min(u,v),max(u,v),g) for u,v,g,l,x in qedges));V=len(cs)
print('dedup',V,len(E),flush=True)
def comps(S,omit=None):
 p=list(range(V))
 def f(u):
  while p[u]!=u:p[u]=p[p[u]];u=p[u]
  return u
 for i in S:
  if i!=omit:
   u,v,g=E[i];p[f(u)]=f(v)
 return [f(v) for v in range(V)]
out=[]
for forbidden in list(range(V)):
 allowed=[i for i,e in enumerate(E) if e[2]!=forbidden];S=set();last={}
 while True:
  C=comps(S);owner={E[i][2]:i for i in S};pred={};queue=[];sink=None
  for i in allowed:
   if i not in S and C[E[i][0]]!=C[E[i][1]]:pred[i]=None;queue.append(i)
  cuts={i:comps(S,i) for i in S}
  for i in queue:
   if i not in S:
    g=E[i][2]
    if g not in owner:sink=i;break
    j=owner[g]
    if j not in pred:pred[j]=i;queue.append(j)
   else:
    C=cuts[i]
    for j in allowed:
     if j not in S and j not in pred and C[E[j][0]]!=C[E[j][1]]:pred[j]=i;queue.append(j)
  if sink is None:last=pred;break
  i=sink
  while i is not None:
   if i in S:S.remove(i)
   else:S.add(i)
   i=pred[i]
  if len(S)==V-1:break
 row={'forbidden':forbidden,'rank':len(S),'tree_edge_indices':sorted(S)}
 if len(S)<V-1:
  R=set(last);A=set(allowed)-R
  r1=V-len(set(comps(A)));r2=len({E[i][2] for i in R});row.update(reachable=sorted(R),minmax_graphic_rank=r1,minmax_partition_rank=r2,minmax_sum=r1+r2)
 out.append(row);print('forbidden',forbidden,'rank',len(S),flush=True)
(D/f'outputs/snakes-exact-{N}.json').write_text(json.dumps({'N':N,'vertices':V,'edges':E,'outcomes':out,'source_bridge':'diagnostic Python transport via source Lemma 9 and Theorem 7; not formally certified'},indent=2))
