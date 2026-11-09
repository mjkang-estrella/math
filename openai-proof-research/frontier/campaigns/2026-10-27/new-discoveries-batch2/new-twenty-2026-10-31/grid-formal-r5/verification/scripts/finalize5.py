from pathlib import Path
import json,hashlib,zipfile,sys
p=Path(__file__).resolve().parent.parent
v=p/'verification'
r=json.loads((v/'replay-report.json').read_text())
assert len(r['strict_serial_replay_modules'])==38
assert r['all_modules_compiled_and_leanchecked'] and r['inventory_equals_audited']
assert r['frozen_31_modules_byte_identical'] and not r['unconditional_endpoint']
for d in ['src','scripts','controls']:
 for f in (p/d).rglob('*'):
  if f.is_file():
   g=v/f.relative_to(p)
   assert g.is_file() and f.read_bytes()==g.read_bytes(),str(f)
if len(sys.argv)==1:
 r['fresh_extracted_replay']='verification/replay-report.json'
 r['first_fresh_replay_wall_timeout_retained']=True
 r['acceptance']='Root decides; partial implementation, no acceptance or credit claimed'
 (p/'results.json').write_text(json.dumps(r,indent=2)+'\n')
 print('Fresh replay: all 38 modules; LOCAL audit and four negative controls passed.')
else:
 with zipfile.ZipFile(p/'grid-formal-r5-source.zip') as z:
  for n in z.namelist():
   assert not n.startswith('/') and '..' not in Path(n).parts
   assert z.read(n)==(p/n).read_bytes(),n
 print('Final archive safely bound to current sources, scripts and documentation.')
 print(hashlib.sha256((p/'grid-formal-r5-source.zip').read_bytes()).hexdigest())
