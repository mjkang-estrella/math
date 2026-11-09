from pathlib import Path
import json,hashlib,itertools
D=Path(__file__).resolve().parents[1]
x=json.loads((D/'extracted.json').read_text());r=json.loads((D/'results.json').read_text());assert len(r)==20 and set(x)==set(r)
for i,o in x.items():
 b=(D/'raw'/f'{i}.jsonl').read_bytes();assert b.endswith(b'\n') and hashlib.sha256(b).hexdigest()==o['provenance']['raw_sha256'];raw=json.loads(b);assert raw['statement']==o['statement'];assert hashlib.sha256(o['statement'].encode()).hexdigest()==o['provenance']['statement_utf8_sha256']
exec(compile((D/'scripts/graphideal.py').read_text().split('rng=random.Random')[0],'ideal-core','exec'))
def private_v(nb):
 n=len(nb);full=(1<<n)-1;best=n
 for ds in range(1,1<<n):
  if any(not (b&ds) for b in nb):continue
  private=[i for i in range(n) if (nb[i]&ds).bit_count()==1]
  if any(not any(nb[i]&ds==1<<u for i in private) for u in range(n) if ds>>u&1):continue
  for choices in itertools.product(*[[i for i in private if nb[i]&ds==1<<u] for u in range(n) if ds>>u&1]):
   cover=0
   for i in choices:cover|=nb[i]
   best=min(best,(cover&~ds).bit_count())
 return best
checks=0
for block in (D/'sources/atlas.dat').read_text().split('GRAPH ')[1:]:
 ls=block.splitlines();n=int(ls[1].split()[1]);
 if not 1<=n<=7:continue
 nb=[1<<i for i in range(n)]
 for l in ls[2:]:
  if l.strip():a,b=map(int,l.split());nb[a]|=1<<b;nb[b]|=1<<a
 v,reg=invariants(nb);assert v==private_v(nb),(ls[0],v,private_v(nb));checks+=1
print('raw provenance and exactly-20-key checks PASS')
print('independent prime-colon versus source private-neighbour formula',checks,'atlas graphs PASS')
# The comparison includes disconnected atlas examples as an extra diagnostic.
print('No Lean endpoint claimed; no Lean trust audit applies.')
