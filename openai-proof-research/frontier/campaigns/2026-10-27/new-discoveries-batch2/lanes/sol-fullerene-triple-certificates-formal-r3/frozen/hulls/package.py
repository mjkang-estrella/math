from pathlib import Path
import json,hashlib,zipfile,shutil,sys,subprocess,re
L=Path(__file__).resolve().parent
MODS=['AuditSupportRank','AuditSupportHulls','Literal','InstanceG','InstanceH','Rank','Hulls','Geometry']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
if sys.argv[1]=='prepare':
 for name in ['Inventory','Audit']:
  t=(L/'frozen/sol-fullerene-rational-polytope-formal-r1'/f'{name}.lean').read_text()
  (L/f'{name}.lean').write_text(t)
  t=t.replace('import InstanceG\nimport InstanceH','import Geometry').replace('[`Literal, `InstanceG, `InstanceH]', '[`Geometry]')
  if name=='Inventory':
   start=t.index(' for (name, info) in env.constants do');end=t.index(' let mut seen',start)
   t=t[:start]+''' for h : idx in [:env.header.moduleNames.size] do
   if env.header.moduleNames[idx] == `Geometry then
     for name in env.header.moduleData[idx]!.constNames do
       let some info := env.find? name | throwError m!"Missing declaration {name}"
       logInfo m!"OWN_DECL {name}"
       logInfo m!"OWN_MODULE {name} Geometry"
       logInfo m!"OWN_SAFETY {name} {info.isUnsafe}"
       if info.isUnsafe then throwError m!"Rejected declaration {name}"
       todo := todo.push name
'''+t[end:]
  else:
   start=t.index(' for (name, _) in env.constants do');end=t.index('\n#audit_all',start)
   t=t[:start]+''' for h : idx in [:env.header.moduleNames.size] do
   if env.header.moduleNames[idx] == `Geometry then
     for name in env.header.moduleData[idx]!.constNames do
       elabCommand (← `(command| #check $(mkIdent name)))
       elabCommand (← `(command| #print axioms $(mkIdent name)))
'''+t[end:]
  t=(L/'frozen/sol-fullerene-rational-polytope-formal-r1'/f'{name}.lean').read_text().replace('import InstanceG\nimport InstanceH','import Geometry').replace('[`Literal, `InstanceG, `InstanceH]', '[`Geometry]')
  for tag in ['Rank','Hulls']:
   tt=t.replace('Geometry',tag)
   if name=='Inventory':
    support=tt.replace('import '+tag,'import Lean.Elab.Command').replace('import Lean\n','import Lean.Elab.Print\n').replace('\n#literal_inventory','')
    (L/f'AuditSupport{tag}.lean').write_text(support)
    (L/f'{name}{tag}.lean').write_text(f'import {tag}\nimport AuditSupport{tag}\n#literal_inventory\n')
   else:
    p=L/f'AuditSupport{tag}.lean'
    p.write_text(p.read_text()+tt[tt.index('open Lean Elab Command in'):].replace('\n#audit_all',''))
    (L/f'{name}{tag}.lean').write_text(f'import {tag}\nimport AuditSupport{tag}\n#audit_all\n')
 shutil.copyfile(L/'frozen/sol-fullerene-rational-polytope-formal-r1/pins.json',L/'pins.json')
 shutil.copyfile('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/lake-manifest.json',L/'administrative/lake-manifest.json')
elif sys.argv[1]=='archive':
 files=[m+'.lean' for m in MODS+['Inventory','Audit','InventoryRank','AuditRank','InventoryHulls','AuditHulls']]+['runner.py','pins.json','RUN.md','administrative/lake-manifest.json']
 h={f:sha(L/f) for f in files}
 (L/'archive-files.json').write_text(json.dumps(h,indent=2)+'\n')
 with zipfile.ZipFile(L/'geometry-source.zip','w',compression=zipfile.ZIP_DEFLATED) as z:
  for f in sorted(files+['archive-files.json']):
   info=zipfile.ZipInfo(f,date_time=(2026,10,30,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16;z.writestr(info,(L/f).read_bytes())
elif sys.argv[1] in ['replay','reconcile']:
 D=L/'replay/fresh';i=0
 while D.exists():i+=1;D=L/f'replay/fresh-{i}'
 if sys.argv[1]=='reconcile':D=L/sys.argv[2]
 else:
  D.mkdir(parents=True,exist_ok=False)
  with zipfile.ZipFile(L/'geometry-source.zip') as z:z.extractall(D)
 for f,h in json.loads((D/'archive-files.json').read_text()).items():assert sha(D/f)==h
 for m in MODS+['Inventory','Audit','InventoryRank','AuditRank','InventoryHulls','AuditHulls']:
  if sys.argv[1]=='reconcile':break
  args=[sys.executable,str(D/'runner.py')]
  if m in MODS:args+=['-o',m+'.olean']
  r=subprocess.run(args+[m+'.lean'],cwd=D,capture_output=True,text=True)
  (D/(m+'-replay.log')).write_text(r.stdout+r.stderr)
  assert r.returncode==0,(m,r.stdout[-3000:],r.stderr)
 logs=[p.read_text() for p in sorted(D.glob('attempt-*.log'))]
 inv='\n'.join(s for s in logs if 'OWN_DECL ' in s);audit='\n'.join(s for s in logs if 'depends on axioms:' in s)
 owned=set(re.findall(r'OWN_DECL (\S+)',inv));covered=set(re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)",audit))
 assert owned==covered and owned
 safety=dict(re.findall(r'OWN_SAFETY (\S+) (\S+)',inv));assert set(safety)==owned and set(safety.values())=={'false'}
 allowed={'propext','Classical.choice','Quot.sound'};observed=set()
 for group in re.findall(r'depends on axioms: \[([^\]]*)\]',audit,re.S):observed|={x.strip() for x in group.split(',') if x.strip()}
 assert observed<=allowed
 for log in D.glob('attempt-*.log'):
  assert not any(s in log.read_text() for s in ['PANIC','error:','sorryAx'])
 (L/'owned-declarations.json').write_text(json.dumps(sorted(owned),indent=2)+'\n')
 (L/'audit.json').write_text(json.dumps(dict(status='PASS',owned_declarations=len(owned),private_generated_included=True,every_owned_axiom_report_present=True,transitive_type_body_safety_counts=[int(x) for x in re.findall(r'TRANSITIVE_SAFE_COUNT (\d+)',inv)],observed_axioms=sorted(observed)),indent=2)+'\n')
 for root in [L]+list((L/'replay').iterdir()):
  for p in root.iterdir():
   if p.suffix in ['.olean','.ilean','.c','.o','.ir'] or '.olean.' in p.name:p.unlink()
 (L/'replay-receipt.json').write_text(json.dumps(dict(status='PASS',scope='Rank extraction and conditional hull/section interfaces; vertex enumeration incomplete',owned_declarations=len(owned),archive_sha256=sha(L/'geometry-source.zip'),serial=True,source_only=True),indent=2)+'\n')
 print('PASS',len(owned))
