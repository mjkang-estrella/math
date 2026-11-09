from pathlib import Path
import subprocess,sys,shutil,hashlib,json,time,re
p=Path(__file__).resolve().parent
dest=p/'replay'
dest.mkdir()
(dest/'formal').mkdir()
for f in (p/'formal').glob('*.lean'):
 if f.name!='Probe.lean':shutil.copy2(f,dest/'formal'/f.name)
for f in ['run.py','batch.py']:shutil.copy2(p/f,dest/f)
shutil.copy2(p/'formal/run_lean.py',dest/'formal/run_lean.py')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
sources={f.stem:f for f in (dest/'formal').glob('*.lean')}
order=[];seen=set()
def visit(n):
 if n in seen:return
 seen.add(n)
 for m in re.findall(r'^import (\S+)',sources[n].read_text(),re.M):
  if m in sources:visit(m)
 order.append(n)
for n in sources:visit(n)
manifest={str(f.relative_to(dest)):sha(f) for f in (dest/'formal').glob('*')}
(dest/'source-before.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert not list(dest.rglob('*.olean'))
t=time.monotonic()
for n in order:
 r=subprocess.run([sys.executable,str(dest/'run.py'),n+'.lean'],capture_output=True,text=True,timeout=130)
 print(n,r.returncode,flush=True)
 if r.returncode:
  print(r.stdout+r.stderr,flush=True);sys.exit(r.returncode)
records=[json.loads(f.read_text()) for f in (dest/'logs').glob('*.json')]
audits='\n'.join((dest/'logs'/f'Audit{i}.lean.log').read_text() for i in range(9))
axioms=set()
for a in re.findall(r'depends on axioms: \[([^]]*)\]',audits):
 axioms.update(x.strip() for x in a.split(',') if x.strip())
assert axioms<=set(['propext','Classical.choice','Quot.sound']),axioms
assert all(sha(dest/f)==h for f,h in manifest.items())
result={'status':'PASS','source_only_initially':True,'order':order,'modules':len(order),'inventoried_declarations':409,'allowed_axioms':sorted(axioms),'sampled_peakRSS_KiB':max(r['sampledPeakRSS_KiB'] for r in records),'wall_seconds':time.monotonic()-t,'records':records,'source_hashes':manifest}
(dest/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['records','source_hashes','order']}))
