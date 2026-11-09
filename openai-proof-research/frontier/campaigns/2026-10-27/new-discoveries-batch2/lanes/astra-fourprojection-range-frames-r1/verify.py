#!/usr/bin/env python3
"""Strict local replay and exact declaration/axiom audit. Writes only inside this lane."""
from pathlib import Path
import subprocess, os, re, json, hashlib, datetime
lane=Path(__file__).resolve().parent
formal=lane/'formal'
logs=lane/'logs'
logs.mkdir(exist_ok=True)
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
packages=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env=dict(os.environ)
env['LEAN_PATH']=str(formal)+':'+':'.join(str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if (p/'.lake/build/lib/lean').is_dir())
mods=['HSBridge','ProjectionFrames','RangeFrames']
for name in mods:
 text=(formal/(name+'.lean')).read_text()
 if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', text):
  raise SystemExit(f'Forbidden proof token in {name}')
version=subprocess.check_output([str(lean),'--version'],text=True).strip()
commands=[]
for name in mods+['Checks','ExplicitChecks']:
 cmd=[str(lean),'-DwarningAsError=true']
 if name in mods: cmd+=['-o',name+'.olean']
 cmd += [name+'.lean']
 with (logs/(name+'.log')).open('w') as log:
  result=subprocess.run(cmd,cwd=formal,env=env,stdout=log,stderr=subprocess.STDOUT)
 commands.append({'module':name,'command':cmd,'returncode':result.returncode})
 if result.returncode:
  raise SystemExit(f'FAIL {name}: see logs/{name}.log')
expected=[]
for name in mods:
 expected += ['FourProjection.'+m.group(1) for m in re.finditer(r'^(?:noncomputable )?(?:theorem|def|abbrev|instance)\s+(\w+)',(formal/(name+'.lean')).read_text(),re.M)]
reports={}
for name in ['Checks','ExplicitChecks']:
 text=(logs/(name+'.log')).read_text()
 report={}
 for decl,items in re.findall(r"'(FourProjection\.\w+)' depends on axioms: \[([^\]]*)\]",text):
  report[decl]=[re.sub(r'\.\{[^}]+\}','',x.strip()) for x in items.split(',') if x.strip()]
 for decl in re.findall(r"'(FourProjection\.\w+)' does not depend on any axioms",text): report[decl]=[]
 assert set(report)==set(expected), ('Incomplete audit',name,set(expected)-set(report))
 assert all(set(items)<={'propext','Classical.choice','Quot.sound'} for items in report.values()),'Nonstandard axioms'
 reports[name]=report
assert reports['Checks']==reports['ExplicitChecks']
result={'status':'PASS','scope':'Source frame infrastructure only; no full-source inequality or acceptance claim.',
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lean_version':version,
 'mathlib_revision_required':'d13f23b723b8a846827a245b89c10fc7d3f11612',
 'commands':commands,'axioms':reports['Checks'],
 'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(formal.glob('*.lean'))}}
(lane/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: all modules and both type/axiom audits; standard three axioms only.')
print(version)
