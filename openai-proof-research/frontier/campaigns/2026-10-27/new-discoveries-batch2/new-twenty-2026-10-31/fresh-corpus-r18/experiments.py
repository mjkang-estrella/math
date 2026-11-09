import json, pathlib, fractions, itertools, collections
P=pathlib.Path(__file__).parent
out={'scope':'all labeled triangle-free H of order 1..7 via triangle-pruned edge recursion; joins H vee I_t for 1<=t<=7 with maximum degree <=7. Records aggregated by (n,e,maxdegree), not all graphs.', 'joins':[],'local_high':[]}
for n in range(1,8):
 edges=list(itertools.combinations(range(n),2)); adj=[0]*n; summary=collections.Counter(); high=collections.Counter()
 def visit(j,e):
  if j==len(edges):
   ds=tuple(sorted(a.bit_count() for a in adj));summary[e,max(ds)]+=1
   if n==7 and e>=11:high[e,ds]+=1
   return
  u,v=edges[j];visit(j+1,e)
  if not adj[u]&adj[v]:
   adj[u]|=1<<v;adj[v]|=1<<u;visit(j+1,e+1);adj[u]^=1<<v;adj[v]^=1<<u
 visit(0,0)
 for (e,degree),count in sorted(summary.items()):
  for t in range(1,8):
   if degree+t<=7:out['joins'].append({'nH':n,'t':t,'eH':e,'maxdegreeH':degree,'labeled_count':count,'density':str(fractions.Fraction(t*e,n+t))})
 for (e,ds),count in sorted(high.items()):out['local_high'].append({'edges':e,'degrees':ds,'labeled_count':count})
out['max_join_density']=str(max(fractions.Fraction(x['density']) for x in out['joins']))
out['circular_check']=[]
for n in range(2,13):
 best=n*n; winners=[]
 for bits in itertools.product('01',repeat=n-1):
  w='0'+''.join(bits); doubled=w+w; squares=set()
  for j in range(n):
   for h in range(1,n//2+1):
    s=doubled[j:j+2*h]
    if s[:h].count('1')==s[h:].count('1'):squares.add(s)
  a=len(squares)
  if a<best:best=a;winners=[]
  if a==best:winners.append(w)
 out['circular_check'].append({'n':n,'minimum':best,'all_minimizers_starting_0':winners})
(P/'experiments.json').write_text(json.dumps(out,indent=2))
print(json.dumps({'join_cases':len(out['joins']),'max_join_density':out['max_join_density'],'local_high':out['local_high'],'circular_ranges':'all binary words starting 0, n=2..12, ALL minimizers retained'}))
