from pathlib import Path
import json,hashlib,zipfile
r=Path(__file__).resolve().parent
(r/'replay.py').write_text('''from pathlib import Path
import subprocess,sys
r=Path(__file__).resolve().parent
for script in ['replay.py','negative.py','check-auditor.py']:
 rc=subprocess.run([sys.executable,'-I',str(r/'scripts'/script)],cwd=r).returncode
 if rc: raise SystemExit(rc)
print('PASS: strict rebuild, one-module kernel checks, full AuditR5, negative controls and auditor safety',flush=True)
''')
(r/'negative-controls/false-pattern.lean').write_text('import ConcreteR2\nexample : (1 : ℚ) ≤ 67027 / 67500 := by norm_num\n')
(r/'negative-controls/false-tree.lean').write_text('import TreeModelsR3\nexample : (3001 : ℚ) / 3000 < 1 := by norm_num\n')
(r/'pins.json').write_text(json.dumps({'lean':'4.34.1','lean_commit':'5045d0056413266e57c625dcd7c365b10e377c52','mathlib':'d13f23b723b8a846827a245b89c10fc7d3f11612'},indent=2)+'\n')
files=[*sorted((r/'formal').glob('*.lean')),*sorted((r/'scripts').glob('*.py')),r/'scripts/modules.json',*sorted((r/'checks').glob('*.lean')),*sorted((r/'negative-controls').glob('*.lean')),r/'replay.py',r/'pins.json']
manifest={str(x.relative_to(r)):hashlib.sha256(x.read_bytes()).hexdigest() for x in files}
(r/'SOURCE-MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n');files.append(r/'SOURCE-MANIFEST.json')
with zipfile.ZipFile(r/'edgepattern-source-only.zip','w',zipfile.ZIP_DEFLATED) as z:
 for f in files:z.write(f,f.relative_to(r))
fresh=r/'fresh-replay';fresh.mkdir()
with zipfile.ZipFile(r/'edgepattern-source-only.zip') as z:
 for i in z.infolist():
  assert not Path(i.filename).is_absolute() and '..' not in Path(i.filename).parts and (i.external_attr>>16)&0o170000!=0o120000
 z.extractall(fresh)
assert not list(fresh.rglob('*.olean'))
(r/'receipts/extraction.json').write_text(json.dumps({'safe_paths':True,'empty_destination':True,'no_oleans':True,'zip_sha256':hashlib.sha256((r/'edgepattern-source-only.zip').read_bytes()).hexdigest(),'sources_match':all(hashlib.sha256((fresh/f).read_bytes()).hexdigest()==h for f,h in manifest.items())},indent=2)+'\n')
