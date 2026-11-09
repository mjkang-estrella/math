import pathlib,json,hashlib,datetime,os
D=pathlib.Path(__file__).resolve().parents[1];h=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((D/'results.json').read_text());res=json.loads((D/'reservation.json').read_text());assert set(map(int,r))==set(res['ids']) and len(r)==20
for k,v in r.items():
 b=(D/'raw'/f'{k}.jsonl').read_bytes();assert b.endswith(b'\n') and h(b)==v['provenance']['raw_sha256'];assert h(v['statement'].encode())==v['provenance']['statement_utf8_sha256'];assert json.loads(b)['statement']==v['statement']
for p in (D/'sources').glob('*/receipt.json'):
 x=json.loads(p.read_text())
 if x.get('sha256'):assert h((p.parent/'body').read_bytes())==x['sha256'],str(p)
registry=json.loads((D/'outputs/registry-screen.json').read_text());assert len(registry['github'])==8
for s in registry['other_registries']:
 if not s['truncated']:print('subtree',s['sha'][:8],s['path_count'],'hits',s['path_matches'][:12])
logs={p.name:json.loads(p.read_text()) for p in (D/'logs').glob('*.receipt.json')}
assert all(x['sampled_group_rss_peak_bytes']<6*1024**3 for x in logs.values())
assert (D/'SUMMARY.md').exists() and (D/'CANDIDATE.md').exists()
files={str(p.relative_to(D)):h(p.read_bytes()) for p in D.rglob('*') if p.is_file() and p.name not in ['artifact-manifest.json','validation.json']}
(D/'outputs/artifact-manifest.json').write_text(json.dumps(files,indent=2)+'\n')
o={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reserved_results':len(r),'http_receipt_count':len(list((D/'sources').glob('*/receipt.json'))),'raw_and_http_hashes':'PASS','registry_searches':len(registry['github']),'numerical_processes':logs,'lean_invocations':0,'accepted_credit':0,'strong_leads':0,'limitation':'Internal artifact consistency only; not independent mathematical review or worldwide prior-art clearance.'}
(D/'outputs/validation.json').write_text(json.dumps(o,indent=2)+'\n');print('PASS',len(files),'files')
