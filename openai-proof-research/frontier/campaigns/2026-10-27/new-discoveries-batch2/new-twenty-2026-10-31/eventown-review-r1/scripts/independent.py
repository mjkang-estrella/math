import itertools,json,pathlib,math
out=pathlib.Path('outputs')
def mul(a,b):return tuple(a[b[i]] for i in range(len(a)))
def inv(a):return tuple(a.index(i) for i in range(len(a)))
def cycles(a):
 seen=set();r=[]
 for i in range(len(a)):
  if i not in seen:
   c=[];j=i
   while j not in seen:seen.add(j);c.append(j);j=a[j]
   r.append(c)
 return r
def good(a,b):return any(len(c)%2==0 for c in cycles(mul(a,inv(b))))
F=[tuple(map(int,s)) for s in ['01234','02143','03412','04321','01243','10234','34210','43201']]
pairs=[{'i':i,'j':j,'quotient':mul(a,inv(b)),'cycles':cycles(mul(a,inv(b))),'pass':good(a,b)} for i,a in enumerate(F) for j,b in enumerate(F) if i<j]
assert len(pairs)==28 and all(p['pass'] for p in pairs)
controls={'identity_self_fails':not good(F[0],F[0]),'identity_3cycle_fails':not good(F[0],(1,2,0,3,4)),'w1w5':mul(F[1],F[5]),'w1w5_outside':mul(F[1],F[5]) not in F}
(out/'pairs.json').write_text(json.dumps({'pairs':pairs,'negative_controls':controls},indent=2))
for n in (2,3,4,5):
 G=list(itertools.permutations(range(n)));e=G[0]; V=[g for g in G if good(g,e)];N=len(V)
 adj=[sum(1<<j for j,b in enumerate(V) if i!=j and good(a,b)) for i,a in enumerate(V)]
 best=0;solutions=[];nodes=0
 def search(R,P):
  global best,solutions,nodes
  nodes+=1
  if not P:
   if len(R)>best:best=len(R);solutions=[]
   if len(R)==best:solutions.append(R)
   return
  # greedy independent color classes give safe clique upper bounds
  order=[];bounds=[];remaining=P;color=0
  while remaining:
   color+=1;avail=remaining
   while avail:
    b=avail&-avail;v=b.bit_length()-1;remaining^=b;avail^=b;avail&=~adj[v];order.append(v);bounds.append(color)
  for v,bound in zip(reversed(order),reversed(bounds)):
   if len(R)+bound<best:return
   bit=1<<v
   if P&bit:search(R+[v],P&adj[v]);P^=bit
 search([], (1<<N)-1)
 subgroup=0
 for s in solutions:
  S={e}|{V[i] for i in s}
  subgroup+=all(mul(a,b) in S for a in S for b in S)
 k=best+1;count=len(solutions)
 r={'n':n,'maximum_size':k,'identity_containing_maxima':count,'identity_subgroup_maxima':subgroup,'identity_non_subgroup_maxima':count-subgroup,'all_maxima':count*math.factorial(n)//k,'all_subgroup_maxima':subgroup,'all_coset_maxima':subgroup*math.factorial(n)//k,'all_non_coset_maxima':(count-subgroup)*math.factorial(n)//k,'search_nodes':nodes,'method':'all maximum cliques containing identity; exhaustive bitset branch and bound with greedy coloring, strict < pruning preserves ties'}
 print(r,flush=True);(out/f'independent-S{n}.json').write_text(json.dumps(r,indent=2))
