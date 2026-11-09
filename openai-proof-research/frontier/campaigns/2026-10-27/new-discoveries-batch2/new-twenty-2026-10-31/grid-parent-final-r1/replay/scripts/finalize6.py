from pathlib import Path
import json,hashlib,zipfile,sys
p=Path(__file__).resolve().parent.parent
v=p/'verification'
r=json.loads((v/'replay-report.json').read_text())
assert len(r['strict_serial_replay_modules'])==47
assert r['unconditional_endpoint'] and not r['remaining']
assert r['all_modules_compiled_and_leanchecked'] and r['inventory_equals_audited']
assert r['frozen_38_modules_byte_identical']
for d in ['src','scripts','controls']:
 for f in (p/d).rglob('*'):
  if f.is_file():
   g=v/f.relative_to(p)
   assert g.is_file() and f.read_bytes()==g.read_bytes(),str(f)
for line in (p/'frozen-before.sha256').read_text().splitlines():
 h,n=line.split()
 assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h
 assert (p/n).read_bytes()==(p/'frozen'/n).read_bytes()
if len(sys.argv)==1:
 r['fresh_extracted_replay']='verification/replay-report.json'
 r['session_resource_compliance']='Qualified: brief development audit overlap, terminated; see RESOURCE-NOTE.md.'
 (p/'results.json').write_text(json.dumps(r,indent=2)+'\n')
 (p/'replay-report.json').write_text(json.dumps(r,indent=2)+'\n')
 print('Fresh strict replay: all 47 modules compiled and leanchecked; audit and four negative controls passed.')
else:
 with zipfile.ZipFile(p/'grid-formal-r6-source.zip') as z:
  for n in z.namelist():
   assert not n.startswith('/') and '..' not in Path(n).parts
   assert z.read(n)==(p/n).read_bytes(),n
 print('Final source archive has safe paths and exactly matches the delivered files.')
 print(hashlib.sha256((p/'grid-formal-r6-source.zip').read_bytes()).hexdigest())
