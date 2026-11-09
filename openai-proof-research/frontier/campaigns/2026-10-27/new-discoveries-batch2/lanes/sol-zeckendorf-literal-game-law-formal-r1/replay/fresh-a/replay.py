from pathlib import Path
import json,hashlib,re,subprocess,sys,zipfile,importlib.util
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
packet=L/'source-only.zip'
results=[]
for tag in ['fresh-a','fresh-b']:
 dest=L/'replay'/tag
 assert not dest.exists()
 dest.mkdir(parents=True)
 with zipfile.ZipFile(packet) as z:
  assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist())
  assert not any(n.endswith(('.olean','.ilean','.ir','.o','.so')) for n in z.namelist())
  z.extractall(dest)
 assert not list(dest.rglob('*.olean'))
 manifest=json.loads((dest/'archive-files.json').read_text())
 for f,h in manifest.items():assert sha(dest/f)==h
 spec=importlib.util.spec_from_file_location('pack',dest/'package.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 assert mod.checkpins()==json.loads((dest/'pins.json').read_text())
 steps=[]
 for args in [['-o','Literal.olean','Literal.lean'],['Inventory.lean'],['Audit.lean']]:
  p=subprocess.run([sys.executable,str(dest/'runner.py'),*args],cwd=dest,stdout=subprocess.DEVNULL)
  assert p.returncode==0,(tag,args)
  receipt=json.loads(sorted(dest.glob('attempt-*.json'))[-1].read_text())
  assert receipt['exit']==0 and receipt['reason'] is None
  steps.append(receipt)
 inv=(dest/'attempt-001.log').read_text();audit=(dest/'attempt-002.log').read_text()
 names=sorted(re.findall(r'^OWN_DECL (\S+)$',inv,re.M))
 assert names==json.loads((dest/'owned-declarations.json').read_text())
 assert len(re.findall(r'^OWN_SAFETY .* false$',inv,re.M))==len(names)
 assert ' true' not in '\n'.join(re.findall(r'^OWN_SAFETY .*$',inv,re.M))
 closure=int(re.search(r'TRANSITIVE_SAFE_COUNT (\d+)',inv)[1])
 ax={n:re.findall(r'[\w.]+',a) for n,a in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",audit,re.M)}
 empty=re.findall(r"^'([^']+)' does not depend on any axioms$",audit,re.M)
 assert set(names)==set(ax)|set(empty)
 assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in ax.values())
 for f,h in manifest.items():assert sha(dest/f)==h
 assert mod.checkpins()==json.loads((dest/'pins.json').read_text())
 for p in dest.rglob('*'):
  if p.suffix in {'.olean','.ilean','.ir','.o','.so'}:p.unlink()
 results.append(dict(extraction=tag,initial_owned_objects=[],steps=steps,declarations=len(names),transitive_safe_constants=closure,inventory_sha256=sha(dest/'attempt-001.log'),audit_sha256=sha(dest/'attempt-002.log'),compiled_objects_removed=True))
assert results[0]['inventory_sha256']==results[1]['inventory_sha256']
assert results[0]['audit_sha256']==results[1]['audit_sha256']
(L/'replay-receipt.json').write_text(json.dumps(dict(status='PASS',packet_sha256=sha(packet),deterministic_diagnostics=True,replays=results),indent=2)+'\n')
print('PASS two fresh source-only serial replays; identical exhaustive inventory and axiom diagnostics')
