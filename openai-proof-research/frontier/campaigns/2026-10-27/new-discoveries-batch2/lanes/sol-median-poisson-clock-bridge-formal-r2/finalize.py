from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for file in ['freeze.json','primary-freeze.json','library-freeze.json','extra-freeze.json']:
 for r in json.loads((L/file).read_text()):
  if r['copy'].startswith('administrative/'):continue
  assert sha(Path(r['original']))==sha(L/r['copy'])==r['sha256']
  rows.append(r)
(L/'binding-after.json').write_text(json.dumps(rows,indent=2)+'\n')
for n in ['FiniteCore.lean','IntegerLeaf.lean']:
 assert (L/n).read_bytes()==(L/'frozen'/n).read_bytes()==(L/'fresh-replay'/n).read_bytes()
r=json.loads((L/'fresh-replay/replay-receipt.json').read_text())
assert r['component_status']=='PASS' and r['source_endpoint_status']=='NOT_PROVED'
# No own compiled artifacts are distributed at lane root; replay artifacts remain as evidence.
for ext in ['*.olean','*.ilean']:
 for p in L.glob(ext):p.unlink()
files={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
(L/'manifest.json').write_text(json.dumps(files,indent=2)+'\n')
print('final manifest',len(files),'files; declarations',r['actual_declaration_count'])
