"""Separate guarded integrity verification; writes only excluded receipt."""
from pathlib import Path
import json,hashlib,tarfile,zipfile
L=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
manifest=json.loads((L/'final-manifest.json').read_text())
files={p.relative_to(L).as_posix() for p in L.rglob('*') if p.is_file() and p.relative_to(L).as_posix() not in ['final-manifest.json','verification-receipt.json']}
assert files==set(manifest)
for n,h in manifest.items():assert sha(L/n)==h,n
bindings=json.loads((L/'bindings.json').read_text())
for r in bindings:assert sha(Path(r['original']))==sha(L/r['copy'])==r['sha256'],r
admin=json.loads((L/'administrative/ledger.json').read_text())
assert (admin['accepted_count'],admin['total_accepted_count'],admin['next_global_outcome_number'])==(9,39,40)
audit=json.loads((L/'replay/full-audit-receipt.json').read_text());assert audit['status']=='PASS' and audit['serial_invocations']==459 and audit['actual_declarations']==35654
assert sha(L/'packet/helper_guard.py')==sha(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')
with tarfile.open(L/'source-packet.tar.gz') as t,zipfile.ZipFile(L/'source-packet.zip') as z:
 internal=json.loads(t.extractfile('SOURCE-MANIFEST.json').read())
 assert set(z.namelist())=={m.name for m in t.getmembers()}==set(internal)|{'SOURCE-MANIFEST.json'}
 for n,h in internal.items():
  assert hashlib.sha256(t.extractfile(n).read()).hexdigest()==hashlib.sha256(z.read(n)).hexdigest()==sha(L/'final-extracted'/n)==h
  assert Path(n).suffix not in ['.olean','.ilean','.ir','.pyc']
with tarfile.open(L/'frozen/input/source-only.tar.gz') as t:
 for m in t:
  if m.name.endswith('.lean'):
   h=hashlib.sha256(t.extractfile(m).read()).hexdigest()
   assert h==sha(L/'packet'/m.name)==sha(L/'replay'/m.name)==sha(L/'final-extracted/formal'/m.name)
ar=json.loads((L/'archive-receipt.json').read_text())
assert ar['tar_sha256']==sha(L/'source-packet.tar.gz')==sha(L/'rebuild.tar.gz')
assert ar['zip_sha256']==sha(L/'source-packet.zip')==sha(L/'rebuild.zip')
for n,h in manifest.items():assert sha(L/n)==h
out=dict(status='PASS',manifest_files=len(manifest),manifest_sha256=sha(L/'final-manifest.json'),scientific_bindings=len(bindings),originals_and_copies_unchanged=True,all_mathematical_source_bytes_unchanged=True,archive_reproduction=ar,strict_serial_replay=audit,PDF='NOTAUTHORED',PDF_QA='QA_NOTPERFORMED',root_replay_prior_adjudication_final_review_acceptance='PENDING',counts='9 additional / 39 total / next40')
(L/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
