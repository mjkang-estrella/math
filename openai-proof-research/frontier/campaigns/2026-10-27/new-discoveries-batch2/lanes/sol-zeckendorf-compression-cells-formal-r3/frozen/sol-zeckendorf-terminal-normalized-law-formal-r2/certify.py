from pathlib import Path
import json,re,hashlib,sys,zipfile,subprocess,importlib.util
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(log):
 names=sorted(re.findall(r'^OWN_DECL (\S+)$',log,re.M))
 safety=dict(re.findall(r'^OWN_SAFETY (\S+) (true|false)$',log,re.M))
 assert names and set(names)==set(safety) and set(safety.values())=={'false'}
 return names
def pins():
 spec=importlib.util.spec_from_file_location('pinscheck',L/'package.py')
 mod=importlib.util.module_from_spec(spec)
 saved=sys.argv;sys.argv=[str(L/'package.py')]
 try:spec.loader.exec_module(mod)
 finally:sys.argv=saved
 assert mod.checkpins()==json.loads((L/'pins.json').read_text())
def audit(log,names):
 ax={n:re.findall(r'[\w.]+',a) for n,a in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",log,re.M)}
 empty=re.findall(r"^'([^']+)' does not depend on any axioms$",log,re.M)
 assert set(names)==set(ax)|set(empty)
 assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in ax.values())
 return [dict(name=n,axioms=ax.get(n,[]),unsafe=False) for n in names]
mode=sys.argv[1]
if mode=='inventory':
 logs=sorted(L.glob('attempt-*.log'))
 log=next(p.read_text() for p in reversed(logs) if 'OWN_DECL ' in p.read_text())
 names=inventory(log)
 (L/'owned-declarations.json').write_text(json.dumps(names,indent=2)+'\n')
 (L/'Audit.lean').write_text('''import Law
import Lean
set_option pp.privateNames true
open Lean Elab Command in
elab "#audit_all" : command => do
 let env ← getEnv
 for (name, _) in env.constants do
  if let some idx := env.getModuleIdxFor? name then
   let mn := env.header.moduleNames[idx.toNat]!
   if mn == `Literal || mn == `Terminal || mn == `Law then
    elabCommand (← `(command| #check $(mkIdent name)))
    elabCommand (← `(command| #print axioms $(mkIdent name)))
#audit_all
''')
 print('declarations',len(names))
elif mode=='pack':
 pins()
 names=json.loads((L/'owned-declarations.json').read_text())
 log=next(p.read_text() for p in reversed(sorted(L.glob('attempt-*.log'))) if 'depends on axioms' in p.read_text())
 rows=audit(log,names)
 inherited=json.loads((L/'frozen/sol-zeckendorf-literal-game-law-formal-r1/owned-declarations.json').read_text())
 assert set(inherited)<=set(names) and len(inherited)==198
 (L/'audit.json').write_text(json.dumps(dict(status='PASS',inherited_count=198,total_count=len(names),declarations=rows,comparison='All 198 inherited declaration names retained; Literal bytes identical. New modules extend the certificate.'),indent=2)+'\n')
 files=['Literal.lean','Terminal.lean','Law.lean','Inventory.lean','Audit.lean','runner.py','package.py','certify.py','RUN.md','owned-declarations.json','pins.json','administrative/lake-manifest.json']
 (L/'archive-files.json').write_text(json.dumps({f:sha(L/f) for f in files},indent=2)+'\n')
 with zipfile.ZipFile(L/'source-only.zip','w',compression=zipfile.ZIP_DEFLATED) as z:
  for f in files+['archive-files.json']:
   info=zipfile.ZipInfo(f,date_time=(2026,10,30,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16
   z.writestr(info,(L/f).read_bytes())
 print('archive',sha(L/'source-only.zip'))
elif mode=='replay':
 results=[]
 for tag in ['fresh-a','fresh-b']:
  dest=L/'replay'/tag;dest.mkdir(parents=True,exist_ok=False)
  with zipfile.ZipFile(L/'source-only.zip') as z:
   assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist())
   assert all(not n.endswith(('.olean','.ilean','.ir','.o','.so')) for n in z.namelist())
   z.extractall(dest)
  manifest=json.loads((dest/'archive-files.json').read_text())
  for f,h in manifest.items():assert sha(dest/f)==h
  steps=[]
  for args in [['-o','Literal.olean','Literal.lean'],['-o','Terminal.olean','Terminal.lean'],['-o','Law.olean','Law.lean'],['Inventory.lean'],['Audit.lean']]:
   p=subprocess.run([sys.executable,str(dest/'runner.py'),*args],cwd=dest,stdout=subprocess.DEVNULL)
   assert p.returncode==0,(tag,args)
   r=json.loads(sorted(dest.glob('attempt-*.json'))[-1].read_text());assert r['exit']==0 and r['reason'] is None;steps.append(r)
  names=inventory((dest/'attempt-003.log').read_text())
  assert names==json.loads((L/'owned-declarations.json').read_text())
  audit((dest/'attempt-004.log').read_text(),names)
  for f,h in manifest.items():assert sha(dest/f)==h
  for p in dest.rglob('*'):
   if p.suffix in {'.olean','.ilean','.ir','.o','.so'}:p.unlink()
  results.append(dict(extraction=tag,steps=steps,declarations=len(names),inventory_sha256=sha(dest/'attempt-003.log'),audit_sha256=sha(dest/'attempt-004.log'),compiled_objects_removed=True))
 assert results[0]['inventory_sha256']==results[1]['inventory_sha256']
 assert results[0]['audit_sha256']==results[1]['audit_sha256']
 pins()
 for p in L.glob('*.olean'):p.unlink()
 (L/'replay-receipt.json').write_text(json.dumps(dict(status='PASS',archive_sha256=sha(L/'source-only.zip'),deterministic_diagnostics=True,replays=results),indent=2)+'\n')
 print('PASS two fresh source-only replays')
