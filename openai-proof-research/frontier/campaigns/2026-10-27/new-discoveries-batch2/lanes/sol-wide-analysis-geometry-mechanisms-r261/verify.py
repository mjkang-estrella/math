from work import *
entries=json.loads((L/'finalmanifest.json').read_text())
assert 'finalmanifest.json' not in entries and 'verification-receipt.json' not in entries
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-{'finalmanifest.json','verification-receipt.json'}
assert actual==set(entries)
for name,h in entries.items():assert sha((L/name).read_bytes())==h,name
sources=json.loads((L/'freeze.json').read_text())
for row in sources:
 assert sha(Path(row['original']).read_bytes())==row['sha256'],row['original']
 assert sha(Path(row['copy']).read_bytes())==row['sha256'],row['copy']
history=json.loads((L/'history-screen.json').read_text())
idx=Path(history['reference_index']);assert sha(idx.read_bytes())==history['reference_sha256']
refs=json.loads(idx.read_text())['verified_references']
for row in refs:assert sha(Path(row['path']).read_bytes())==row['sha256'],row['path']
assert json.loads((L/'exactchecks.json').read_text())['difference']=='0'
assert json.loads((L/'latticechecks.json').read_text())['exact_controls']==list(range(31))
receipt=dict(status='PASS',time=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),files=len(entries),scientific_bindings=len(sources),immutable_history_references=len(refs),counts='9/39/next40 unchanged; uncredited pending review',limits='specified helper_guard AS/groupRSS512MiB CPU210s wall230s; thread env1; no cap raises')
dump('verification-receipt.json',receipt);print(json.dumps(receipt,indent=2))
