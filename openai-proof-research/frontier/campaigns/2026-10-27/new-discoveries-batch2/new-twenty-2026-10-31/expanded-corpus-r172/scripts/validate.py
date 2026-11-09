import pathlib,json,hashlib,itertools,math,collections
D=pathlib.Path(__file__).resolve().parents[1];rows=json.loads((D/'extracted.json').read_text());reserved=json.loads((D/'reservation.json').read_text())['ids'];res=json.loads((D/'results.json').read_text())
assert set(map(int,res))==set(reserved) and len(res)==20
for i,r in rows.items():
 b=(D/'raw'/f'{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==r['provenance']['raw_sha256'];assert hashlib.sha256(r['statement'].encode()).hexdigest()==r['provenance']['statement_utf8_sha256']
# Independent direct path search validates the multipartite longest-path formula.
checks=0
for counts in itertools.product(range(4),repeat=3):
 n=sum(counts)
 if not 1<=n<=7:continue
 colors=[i for i,c in enumerate(counts) for _ in range(c)];dp={1<<v:{v} for v in range(n)};longest=1
 for mask in range(1,1<<n):
  ends=dp.get(mask,set())
  if ends:longest=max(longest,mask.bit_count())
  for v in ends:
   for w in range(n):
    if not mask>>w&1 and colors[v]!=colors[w]:dp.setdefault(mask|1<<w,set()).add(w)
 assert longest==min(n,2*(n-max(counts))+1);checks+=1
pf=json.loads((D/'outputs/pf-search.json').read_text());assert pf['tested']==795
for shape,t,expected in [([1,1,1],3,[0,1,0]),([2,2],3,[0,3,0,0]),([2,2],4,[0,0,1,0])]:
 o=next(x for x in pf['records'] if x['parts']==shape and x['t_vertices']==t);assert o['reduced_betti_mod2']==expected and o['reduced_betti_mod3']==expected
for p in ['pebbling-search.json','pebbling-extended.json']:
 o=json.loads((D/'outputs'/p).read_text());assert all(r['all_resolved'] for r in o['graphs']);assert not o['violations']
# Direct enumeration validates the closed-form threshold-family degree distribution.
checks2=0
for n,k,s in [(8,3,1),(9,3,1),(13,3,2)]:
 for j in range(1,k+1):
  m=(s+1)*j-1
  family=[set(t) for t in itertools.combinations(range(n),k) if sum(v<m for v in t)>=j]
  for r in range(1,k):
   for R in itertools.combinations(range(n),r):
    z=sum(v<m for v in R);actual=sum(set(R)<=F for F in family)
    C=lambda a,b:math.comb(a,b) if 0<=b<=a else 0
    expected=sum(C(m-z,a)*C(n-m-r+z,k-r-a) for a in range(max(0,j-z),k-r+1));assert actual==expected;checks2+=1
receipt={'passed':True,'raw_records':20,'independent_multipartite_path_checks':checks,'independent_threshold_degree_checks':checks2,'homology_sanity_cases':3,'pebbling_all_target_thresholds_resolved':True,'limitation':'Diagnostic validation only; no Lean or general theorem.'}
(D/'outputs/validation.json').write_text(json.dumps(receipt,indent=2));print(receipt)
