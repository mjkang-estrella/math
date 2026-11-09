import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids']
assert set(map(int,r))==set(ids) and len(r)==20
for i,o in r.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();p=o['provenance']
 assert b.endswith(b'\n') and hashlib.sha256(b).hexdigest()==p['raw_sha256']
 assert hashlib.sha256(o['statement'].encode()).hexdigest()==p['statement_utf8_sha256']
 assert o['credit']==0
gs=json.loads((D/'outputs/graphs.json').read_text())
assert [(x['n'],len(x['rows'])) for x in gs]==[(3,2),(4,6),(5,21),(6,112)]
assert all(not x['facet_failures'] and all(not z['derivative_failures'] for z in x['rows']) for x in gs)
checks=[]
for k in [3,5]:
 b=json.loads((D/f'outputs/inverse-{k}.json').read_text());s={x['n']:x['sg'] for x in b};m=(k-1)//2
 if k==5:
  t=json.loads((D/'outputs/inverse-split-5.json').read_text());assert all(s[x['n']]==x['sg'] for x in t if x['n'] in s);s={x['n']:x['sg'] for x in t}
 shift=reflect=0
 for n,v in s.items():
  assert v<=1
  if n+2+3*m in s:assert s[n+2+3*m]==(v^(m%2));shift+=1
  if 2+5*m-n in s:assert s[2+5*m-n]==(v^(m%2));reflect+=1
 checks.append(dict(k=k,completed_max_n=max(s),shift_pairs=shift,reflection_pairs=reflect))
assert all(not row['failures'] for n in json.loads((D/'outputs/permutations.json').read_text()) for row in n['rows'])
f=json.loads((D/'outputs/finite.json').read_text());assert f['375232']['counterexample']
assert len(json.loads((D/'outputs/registry-screen.json').read_text())['github_searches'])==8
out={'ids':20,'raw_hashes':'PASS','statement_hashes':'PASS','graph_checks':'PASS: 141 connected classes, corrected rational run','inverse_overlap_and_literal_bounded_identities':checks,'permutation_checks':'PASS through n=8, k=3..6','EF1_allocation_check':'exactly two feasible, neither EF1','Lean':'not attempted; no eligible candidate','credit':0}
(D/'outputs/validation.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
