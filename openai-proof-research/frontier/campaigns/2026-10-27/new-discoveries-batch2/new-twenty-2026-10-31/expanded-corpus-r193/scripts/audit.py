import pathlib,json,hashlib,collections
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((D/'results.json').read_text());res=json.loads((D/'reservation.json').read_text());assert set(r)=={str(i) for i in res['ids']} and len(r)==20
for i,z in r.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();assert b.endswith(b'\n') and sha(b)==z['provenance']['raw_sha256'];assert sha(z['statement'].encode())==z['provenance']['statement_utf8_sha256']
n=0
for p in (D/'sources').glob('*.receipt.json'):
 o=json.loads(p.read_text());b=p.with_name(p.name.replace('.receipt.json','.body'))
 if 'sha256' in o:assert sha(b.read_bytes())==o['sha256']
 n+=1
logs={p.stem:json.loads(p.read_text()) for p in (D/'logs').glob('*.json')}
out={'id_count':len(r),'http_receipts':n,'outcome_counts':dict(collections.Counter(z['outcome'] for z in r.values())),'raw_and_http_hashes_verified':True,'numerical_logs':logs,'lean_invocations':0,'qualification':'No new full-scope proof; no accepted credit. Coverage and sequencing exceptions in SUMMARY.md.'}
(D/'outputs/audit.json').write_text(json.dumps(out,indent=2));print('IDs',len(r),'receipts',n,'all stored hashes verified','logs',len(logs))
manifest={str(p.relative_to(D)):sha(p.read_bytes()) for folder in ['scripts','raw','outputs'] for p in (D/folder).rglob('*') if p.is_file() and p.name!='artifact-hashes.json'}
manifest.update({p:sha((D/p).read_bytes()) for p in ['results.json','SUMMARY.md','CANDIDATE.md']})
(D/'outputs/artifact-hashes.json').write_text(json.dumps(manifest,indent=2))
