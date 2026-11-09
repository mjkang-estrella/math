import pathlib,json,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text());ids=set(map(str,json.loads((D/'reservation.json').read_text())['ids']));assert set(r)==ids and len(r)==20
for i,x in r.items():
 raw=(D/'raw'/(i+'.jsonl')).read_bytes();assert raw.endswith(b'\n');assert hashlib.sha256(raw).hexdigest()==x['provenance']['raw_sha256'];assert hashlib.sha256(x['statement'].encode()).hexdigest()==x['provenance']['statement_utf8_sha256'];assert x['discovery_credit']==0
reg=json.loads((D/'outputs/registry-screen.json').read_text());assert len(reg['github_queries'])==8
reg['limitations']=['Eight queries used arXiv IDs plus lean, except the final equitable-matroid phrase; expanded author/name repository queries were not performed within this query budget. This does not fully satisfy the brief name/author query request.','Generic Ling substring and Cartesian substrings create unrelated hits. All raw excerpts retained; no exact target proof identified and no semantic clearance claimed.','Current D5/Problems/preprints keyword-hit list is outputs/tree-keyword-hits.json; those generic-hit proof bodies were not audited.','No strong candidate survived; no affirmative worldwide-priority assertion.']
(D/'outputs/registry-screen.json').write_text(json.dumps(reg,indent=2,ensure_ascii=False)+'\n')
valid={'reserved_entries':20,'raw_line_hash_checks':20,'statement_hash_checks':20,'github_repository_queries':8,'credit_claimed':0,'lean_invocations':0,'strong_candidates':0,'incomplete_work':'Several finite-target searches and complete citation/version proof-body comparison remain absent, as explicitly stated in results.json and SUMMARY.md.'}
(D/'outputs/validation.json').write_text(json.dumps(valid,indent=2)+'\n')
manifest={}
for p in sorted(D.rglob('*')):
 if p.is_file() and p.name!='manifest.json' and '__pycache__' not in p.parts:manifest[str(p.relative_to(D))]=hashlib.sha256(p.read_bytes()).hexdigest()
(D/'outputs/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(valid)
