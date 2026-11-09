from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[]
manifest=json.loads((L/'manifest.json').read_text())
for r in manifest['files']:
 p=L/r['path']
 if not p.is_file() or h(p)!=r['sha256'] or p.stat().st_size!=r['size']:errors.append(['manifest',r['path']])
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in manifest['excludes']}
if actual!={r['path'] for r in manifest['files']}:errors.append(['file_set'])
for r in json.loads((L/'bindings.json').read_text()):
 for p in [Path(r['original']),L/r['copy']]:
  if not p.is_file() or h(p)!=r['sha256']:errors.append(['frozen_binding',str(p)])
for r in json.loads((L/'source-bindings.json').read_text()):
 if h(L/r['file'])!=r['sha256']:errors.append(['source',r['file']])
for r in json.loads((L/'history-bindings.json').read_text()):
 p=Path(r['path'])
 if not p.is_file() or h(p)!=r['sha256']:errors.append(['history_changed',str(p)])
for r in json.loads((L/'body-access.json').read_text()):
 if 'file' in r and h(L/r['file'])!=r['sha256']:errors.append(['body',r['file']])
 if 'text_sha256' in r and h((L/r['file']).with_suffix('.txt'))!=r['text_sha256']:errors.append(['text',r['file']])
ledger=json.loads((L.parent.parent/'ledger.json').read_text())
counts=[ledger[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']]
if counts!=[9,39,40]:errors.append(['counts',counts])
receipt=dict(status='PASS' if not errors else 'FAIL',errors=errors,manifest_sha256=h(L/'manifest.json'),verified_files=len(manifest['files']),frozen_original_copy_after_check=True,time=datetime.datetime.now(datetime.timezone.utc).isoformat(),separate_process=True,counts=counts)
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));raise SystemExit(bool(errors))
