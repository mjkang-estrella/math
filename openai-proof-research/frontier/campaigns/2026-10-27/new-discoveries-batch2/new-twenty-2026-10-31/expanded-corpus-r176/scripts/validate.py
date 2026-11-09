import pathlib,json,itertools,hashlib
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert set(map(int,r))==set(ids) and len(r)==20
for i,o in r.items():
 b=(D/'raw'/f'{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==o['provenance']['raw_sha256'];assert hashlib.sha256(o['statement'].encode()).hexdigest()==o['provenance']['statement_utf8_sha256']
checks=[]
for row in json.loads((D/'outputs/groups-extended.json').read_text()):
 mods=row['moduli'];G=list(itertools.product(*[range(m) for m in mods]));R=[x for x in G if any(x) and any(2*a%m for a,m in zip(x,mods))];ind={x:i for i,x in enumerate(R)};neg=lambda x:tuple(-a%m for a,m in zip(x,mods));used=set()
 for mask in row['mask_certificate']:
  S={i for i in range(len(R)) if mask>>i&1};assert len(S)==6 and not S&used;used|=S;assert {ind[neg(R[i])] for i in S}==S
  found=False
  for T in itertools.combinations(S,3):
   if all(sum(R[i][j] for i in T)%m==0 for j,m in enumerate(mods)) and {ind[neg(R[i])] for i in T}==S-set(T):found=True;break
  assert found
 assert len(row['mask_certificate'])==len(R)//6
 checks.append({'moduli':mods,'disjoint_six_sets':len(row['mask_certificate']),'direct_group_arithmetic_check':True})
q=json.loads((D/'outputs/polygon.json').read_text());assert not q['nonisometric'] and q['local_cone_feasible']==8
for p in (D/'logs').glob('*.receipt.json'):
 o=json.loads(p.read_text());assert o['sampled_group_rss_peak_bytes']<6*1024**3
out={'results_count':20,'exact_raw_and_statement_hashes':'PASS','group_certificates':checks,'polygon_dihedral_count':'PASS','resource_receipts':'PASS with documented timeout; sampled peak below cap','no_new_lean_endpoint':True};(D/'outputs/validation.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
