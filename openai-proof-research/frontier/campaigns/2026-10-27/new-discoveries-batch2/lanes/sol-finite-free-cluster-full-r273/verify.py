from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'final-manifest.json').read_text());checks=[]
for row in manifest['files']:
 p=L/row['path'];assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'];checks.append(row['path'])
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in manifest['excludes']}
assert actual==set(checks)
sources=json.loads((L/'source-bindings.json').read_text())
sources += [json.loads(s) for s in (L/'access.jsonl').read_text().splitlines() if '"sha256"' in s]
for row in sources:
 assert sha(Path(row['original']))==sha(Path(row['copy']))==row['sha256']
 if 'text_sha256' in row:assert sha(Path(row['copy']).with_suffix('.txt'))==row['text_sha256']
# Bind the actual reused PDF to r266's primary response too, without recopying history.
R=L.parent/'sol-wide-new-source-mechanisms-r266'
assert sha(R/'primary/1811.06382v1.pdf')==sha(R/'science/1811.06382v1.pdf')==sha(L/'frozen/science--1811.06382v1.pdf')
assert not (L/'PROOF.md').exists()
for f,count in [('cluster-check.json',2016),('separated-cluster-check.json',2016),('threecluster-check.json',828)]:
 assert json.loads((L/f).read_text())['tested']==count
for row in json.loads((L/'replay-results.json').read_text()):assert row['exit']==0
receipt={'status':'PASS','time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(L/'final-manifest.json'),'manifest_files_checked':len(checks),'source_original_copy_pairs_checked':len(sources),'r266_primary_science_local_pdf_equal':True,'administrative_policy':'snapshots only; no live ledger equality demanded','result_scope':'integrity/replay verification, NOT mathematical endpoint or novelty acceptance','credit':0,'counts':[9,39,40],'separate_guarded_process':True}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
