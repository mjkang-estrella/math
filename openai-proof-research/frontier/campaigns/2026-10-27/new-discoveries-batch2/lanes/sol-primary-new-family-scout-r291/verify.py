from run import *
m=json.loads((L/'MANIFEST.json').read_text());assert 'MANIFEST.json' not in m and 'verification-receipt.json' not in m
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']}
assert actual==set(m)
for n,h in m.items():assert sha(L/n)==h,n
for r in json.loads((L/'source-bindings.json').read_text()):assert sha(pathlib.Path(r['local']))==r['sha256']
for line in (L/'derived.jsonl').read_text().splitlines():
 r=json.loads(line);assert sha(pathlib.Path(r['source']))==r['sha256'];assert sha(pathlib.Path(r['text']))==r['text_sha256']
for r in json.loads((L/'administrative-bindings.json').read_text()):assert sha(pathlib.Path(r['copy']))==r['sha256']
assert not (L/'PROOF.md').exists()
assert json.loads((L/'context-reconciliation.json').read_text())['accepted_count']==9
dump('verification-receipt.json',{'status':'PASS','time':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(L/'MANIFEST.json'),'files':len(m),'sources_and_text_derivatives':'PASS','administrative_snapshot_integrity':'PASS; live admin files not asserted immutable','separate_process_after_final_writes':True,'scope':'artifact integrity only; no full mathematical or novelty certification','no_proof_file':True})
print('PASS',len(m),'manifest files; all frozen sources and derivatives intact')
