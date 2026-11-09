import itertools,pathlib,json,time
D=pathlib.Path(__file__).resolve().parents[1]
def comp(n,s):
 if n==1:yield(s,);return
 for i in range(s+1):
  for q in comp(n-1,s-i):yield(i,)+q
out=[];start=time.monotonic()
for n in range(2,10):
 for kind in ['cyclic']+(['xor'] if n in [4,8] else []):
  table=[[(r+c)%n if kind=='cyclic' else r^c for c in range(n)] for r in range(n)]
  reachable=set();perms=0
  # all permutations on rows1..n-1, unassigned last column. Missing row0 suffices by group translation, with color translation below.
  for cols in itertools.permutations(range(n),n-1):
   counts=[0]*n
   for r,c in enumerate(cols,1):counts[table[r][c]]+=1
   reachable.add(tuple(counts));perms+=1
  translated=set()
  for c in reachable:
   for a in range(n):translated.add(tuple(c[(v-a)%n if kind=='cyclic' else v^a] for v in range(n)))
  missing=[c for c in comp(n,n-1) if c not in translated]
  out.append({'order':n,'group':kind,'partial_permutations_missing_row0':perms,'attainable_multiplicity_vectors':len(translated),'missing_vectors':missing})
r={'scope':'group addition Latin squares cyclic n2..9 and elementary abelian2 n4,8, all prescribed n-1 multiplicities; group row-translation reduction is explicit','records':out,'seconds':time.monotonic()-start,'limitation':'Only classical group tables; any inherited classical obstruction would carry zero-credit risk. No general Latin-square assertion.'}
(D/'outputs/latin-search.json').write_text(json.dumps(r,indent=2));print(r)
