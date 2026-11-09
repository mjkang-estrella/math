"""Run in a SEPARATE helper_guard invocation after finalize.py."""
from pathlib import Path
import json,hashlib,subprocess,sys,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'final-manifest.json').read_text())
bad=[]
for r in manifest:
 p=L/r['path']
 if not p.is_file() or sha(p)!=r['sha256'] or p.stat().st_size!=r['bytes']:bad.append(r['path'])
external=[];seen=set()
for n in ['frozen-references.json','expanded-alias-bindings.json','active-lane-bindings.json']:
 for r in json.loads((L/n).read_text()):
  p=Path(r['path']);key=(str(p),r['sha256'])
  if key in seen:continue
  seen.add(key)
  if not p.is_file() or sha(p)!=r['sha256']:external.append(str(p))
for r in json.loads((L/'prior-campaign-aliases.json').read_text())['references']:
 p=Path(r['path'])
 if not p.is_file() or sha(p)!=r['sha256']:external.append(str(p))
primary=[]
for line in (L/'source-receipts.jsonl').read_text().splitlines():
 r=json.loads(line);name=r.get('file',r.get('derived'))
 if name is None:name=Path(r['path']).name
 p=L/'sources'/name
 if sha(p)!=r['sha256']:primary.append(name)
r=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,text=True,timeout=60)
for entry in manifest:
 if sha(L/entry['path'])!=entry['sha256']:bad.append('after replay:'+entry['path'])
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'manifest_sha256':sha(L/'final-manifest.json'),'manifest_entries':len(manifest),
 'bad_lane_files':bad,'changed_external_scientific_references':external,
 'bad_primary_or_derived':primary,'external_reference_bindings_checked':len(seen),
 'replay_exit':r.returncode,'replay_stdout':r.stdout.strip(),'replay_stderr':r.stderr.strip(),
 'pass':not bad and not external and not primary and r.returncode==0,
 'scope':'Integrity and exact-control replay only, not acceptance, novelty clearance or discovery credit.'}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2));sys.exit(0 if receipt['pass'] else 1)
