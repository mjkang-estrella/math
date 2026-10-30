from pathlib import Path
import json,sys,subprocess,datetime,hashlib
R=Path(__file__).resolve().parent;D=R/'fresh-extraction';sys.path.insert(0,str(D))
from audit_tools import sha,audit,dependencies,MODS
manifest=json.loads((D/'manifest.json').read_text())
for n,h in manifest.items():assert sha(D/n)==h
assert not list(D.rglob('*.olean'))
pins=json.loads((D/'pins.json').read_text())
assert sha(Path(pins['lean_binary']))==pins['lean_sha256']
# Execute only the pin parser prefix verbatim; do not mutate the frozen verifier.
v=(D/'verify_inputs.py').read_text();exec(compile(v.split("for row in json.loads((R/'originals-before.json')")[0],str(D/'verify_inputs.py'),'exec'),{'__file__':str(D/'verify_inputs.py')})
drifts=[]
for row in json.loads((D/'input-records.json').read_text()):
 assert sha(D/row['copy'])==row['sha256']
 h=sha(Path(row['original']))
 if h!=row['sha256']:drifts.append(dict(row,actual_sha256=h))
for row in json.loads((D/'originals-before.json').read_text()):assert sha(Path(row['path']))==row['sha256']
assert len(drifts)==1 and drifts[0]['original'].endswith('/NEXT.md'),drifts
for row in json.loads((D/'dependency-hashes.json').read_text()):assert sha(Path(row['path']))==row['sha256']
(D/'logs').mkdir(exist_ok=True);steps=[]
with (R/'strict-modules.log').open('w') as log:
 for m in MODS+['FullAudit']:
  print('BUILD',m,flush=True)
  p=subprocess.run([sys.executable,str(D/'guard.py'),m],stdout=log,stderr=subprocess.STDOUT);assert p.returncode==0,m
  steps.append(json.loads((D/'logs'/f'{m}.json').read_text()))
  if m!='FullAudit':assert (D/'logs'/f'{m}.log').stat().st_size==0
rows=audit(D);assert rows==json.loads((D/'actual-declarations.json').read_text());assert len(rows)==139
assert dependencies(D)==json.loads((D/'dependency-hashes.json').read_text())
for n,h in manifest.items():assert sha(D/n)==h
(R/'strict-modules-receipt.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',mandatory_packet_replay='HOLD: live NEXT.md drift',input_drifts=drifts,steps=steps,declaration_count=len(rows),declarations=rows),indent=2)+'\n')
