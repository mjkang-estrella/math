import pathlib,json,hashlib
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186')
p=L/'results.json';data=json.loads(p.read_text());r=data['339956'];r['outcome']='excluded_published_refutation_bridge';r['reason']+=' Final citing-work follow-up found Bolognini--Sentinelli arXiv:2605.24732, Theorem 4.2: S_(d,d+13) is not extendably shellable for d>=3. By the original source Corollary 3.7, the universal inclusion conjecture implies Simon extendable shellability, so its general negation already follows from this published primary counterexample. Theorem 4.2 and proof were read. This is an exclusion, not a new lane solution.';r['remaining_gap']='No novelty: original Corollary 3.7 plus the May 2026 counterexample gives the general negative answer. No claim of a new explicit clutter certificate.';r['credit_risk']='Zero: existing published refutation plus source bridge.'
data['338558']['mathematical_attempts']='All 299 pairs n=2..24, l=1..n at the predicted rank tested over F_1009; every Jacobian had full row rank. Deterministic seed 186, separate seed resets for ranges 2..12 and 13..24. Complete logs and outputs retained.'
for r in data.values():r['literature_receipts']='sources/web-literature-01.json through web-literature-10.json; dated HTTP receipts in sources/'
p.write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
s=L/'SUMMARY.md';t=s.read_text().replace('seven excluded routes and thirteen parked routes','eight excluded routes and twelve parked routes').replace('The thirteen parked entries','The twelve parked entries').replace('339956: exact forward closure','339956: ultimately excluded: the source Corollary 3.7 plus Bolognini--Sentinelli arXiv:2605.24732 Theorem 4.2 (May 2026), whose statement and proof were read, already refute the universal inclusion through the published failure of Simon extendable shellability. Before this final citation follow-up, exact forward closure').replace('No obstruction found.','No obstruction found.').replace('sources/web-literature-01.json through web-literature-09.json','sources/web-literature-01.json through web-literature-10.json')
s.write_text(t)
ids=set(map(str,json.loads((L/'reservation.json').read_text())['ids']));assert set(data)==ids and len(data)==20
prov=json.loads((L/'outputs/provenance.json').read_text())
for i,r in prov.items():
 raw=(L/f'sources/{i}.raw.jsonl').read_bytes();assert raw.endswith(b'\n');assert hashlib.sha256(raw).hexdigest()==r['raw_sha256'];assert hashlib.sha256(json.loads(raw)['statement'].encode()).hexdigest()==r['statement_sha256']
rank=[]
for name in ['ranks.json','ranks13-24.json']:rank+=json.loads((L/'outputs'/name).read_text())
assert len(rank)==299 and all(r['jacobian_rank']==r['edges'] for r in rank)
assert not json.loads((L/'outputs/validation.json').read_text())['cycles']['violations']
manifest={str(f.relative_to(L)):{'bytes':f.stat().st_size,'sha256':hashlib.sha256(f.read_bytes()).hexdigest()} for f in L.rglob('*') if f.is_file() and f.name!='artifact-manifest.json'}
(L/'outputs/artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Verified exactly 20 IDs, raw provenance, 299 full-rank pairs, no cycle violations; manifest files',len(manifest))
