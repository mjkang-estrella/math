import itertools,pathlib,json,math,hashlib
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in [4,5,6]:
 E=list(itertools.combinations(range(n),2));tested=0;fails=[]
 for mask in range(1<<len(E)):
  adj=[set() for _ in range(n)]
  for i,(v,w) in enumerate(E):
   if mask>>i&1:adj[v].add(w);adj[w].add(v)
  if min(map(len,adj))<4:continue
  tested+=1
  ok=any(all(p[(j+1)%n] in adj[p[j]] for j in range(n)) for q in itertools.permutations(range(1,n)) for p in [(0,)+q])
  if not ok:fails.append(mask)
 out.append({'n':n,'all_labeled_minimum_degree_4_graphs':tested,'nonhamiltonian':fails,'note':'superclass of 4-connected toroidal graphs; no torus embedding recognition claimed'})
P={3:1}
for n in range(4,10):P[n]=2**(n-3)*P[n-1]
counts={3:1,4:2,5:6,6:40,7:560,8:17024,9:1066496}
for n in range(4,10):out.append({'m':n,'published_N':counts[n],'twice_lower_bound':P[n]+P[n-1],'twice_upper_bound':P[n]+2*P[n-1],'bounds_hold':P[n]+P[n-1]<=2*counts[n]<=P[n]+2*P[n-1]})
(D/'outputs/final-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
# Record byte identities of inherited read-only inputs and cached registry scopes.
refs=[D.parent/'ledger.json',D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json',D.parent/'fresh-corpus-r10/sources/registry-preprints.json']
r=[]
for p in refs:
 if p.exists():r.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size})
(D/'outputs/inherited-inputs.json').write_text(json.dumps(r,indent=2)+'\n')
