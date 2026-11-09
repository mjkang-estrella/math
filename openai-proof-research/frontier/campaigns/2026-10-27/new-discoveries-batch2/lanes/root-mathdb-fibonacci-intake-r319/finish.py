from pathlib import Path
import hashlib,json,sys
P=Path(__file__).resolve().parent; B=P.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,o): (P/n).write_text(json.dumps(o,indent=2)+'\n')
if sys.argv[1]=='build':
 bindings=json.loads((P/'bindings.json').read_text())
 manifest=json.loads((P/'frozen/pi-fibonacci-minima-source-hypothesis-r312--MANIFEST.json').read_text())
 for row in manifest['files']:
  s=B/'pi-fibonacci-minima-source-hypothesis-r312'/row['path']
  d=P/'frozen/payload'/row['path']; d.parent.mkdir(parents=True,exist_ok=True)
  h=sha(s)
  if not d.exists(): d.write_bytes(s.read_bytes())
  assert sha(d)==h
  bindings.append({'original':str(s),'copy':str(d),'sha256':h})
 write('bindings.json',bindings)
 write('intake.json',{'id':371202,'disposition':'retire_public_resolution_and_campaign_duplicate','basis':'completed delegated source investigation; no new acceptance','credit':0,'accepted_total':39,'additional':9,'technical_statement_review_total_unchanged':133,'qualifications':['Child manifest lists roles, not hashes; child receipt checks file existence, input bindings and arithmetic, not payload hash continuity.','Root freezes and verifies delivered bytes now; this does not retroactively establish delivery-time hashes or independently audit mathematics.','Source correction and prior in-house certificate are reported by the delegate; no claim of exhaustive current-prior clearance.'],'allocation':{'r312':'completed; retired','r313':'allocated; no terminal notification received','r317':'allocated; no terminal notification received','r320':'next reserved breadth launch; see returned tool receipt for actual status'},'next_breadth_reservation':'root-mathdb-next-breadth-r318/reserved-ids.json'})
 write('manifest.json',{str(p.relative_to(P)):sha(p) for p in sorted(P.rglob('*')) if p.is_file() and p.name not in ('manifest.json','verification-receipt.json')})
 print('Built root snapshot and qualified retirement intake.')
else:
 bindings=json.loads((P/'bindings.json').read_text())
 for r in bindings: assert sha(Path(r['original']))==sha(Path(r['copy']))==r['sha256'],r
 m=json.loads((P/'manifest.json').read_text())
 for n,h in m.items(): assert sha(P/n)==h,n
 actual={str(p.relative_to(P)) for p in P.rglob('*') if p.is_file() and p.name not in ('manifest.json','verification-receipt.json')}
 assert actual==set(m)
 write('verification-receipt.json',{'status':'PASS','frozen_bindings':len(bindings),'manifest_files':len(m),'credit':0,'scope':'Delivered-byte snapshot integrity; no independent mathematical or historical audit'})
 print(json.dumps({'status':'PASS','bindings':len(bindings),'files':len(m)}))
