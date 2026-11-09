import itertools,pathlib,json,math
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in range(4,8):
 q=n+1;perms=list(itertools.permutations(range(q)));idx={p:i for i,p in enumerate(perms)}
 edges=[(0,q-1)]+[(i-1,i) for i in range(1,q)]
 neigh=[]
 for a,b in edges:
  ns=[]
  for p in perms:
   z=list(p);z[a],z[b]=z[b],z[a];ns.append(idx[tuple(z)])
  neigh.append(ns)
 cycles={};lengths={}
 for i,j in itertools.combinations(range(q),2):
  seen=set();ls=[]
  for v in range(len(perms)):
   if v in seen:continue
   stack=[v];seen.add(v);sz=0
   while stack:
    x=stack.pop();sz+=1
    for y in (neigh[i][x],neigh[j][x]):
     if y not in seen:seen.add(y);stack.append(y)
   ls.append(sz)
  cycles[i,j]=len(ls);lengths[str((i,j))]=sorted(set(ls))
 best=max(sum(cycles[tuple(sorted((order[i],order[(i+1)%q])))] for i in range(q)) for tail in itertools.permutations(range(1,q)) for order in [(0,)+tail])
 genus=1+(n-1)*len(perms)//4-best//2
 out.append({'n':n,'vertices':len(perms),'max_bicolored_sum':best,'genus':genus,'source_formula':1+math.factorial(n+1)*(n-3)//8,'cycle_lengths':lengths})
r={'interpretation':'Permutation graph with adjacent-position transpositions and endpoint transposition; tests the source graph combinatorics, not manifold realization or genus minimality among all crystallizations','records':out,'credit':0}
(D/'outputs/torus-search.json').write_text(json.dumps(r,indent=2));print(r)
