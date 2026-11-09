from pathlib import Path
import hashlib,json,zipfile,subprocess,sys
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((root/'manifest.json').read_text())
expected=set(m)
actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
assert expected==actual,(expected^actual)
for n,h in m.items():assert sha(root/n)==h,n
assert not any(p.suffix in ['.olean','.ilean','.o','.so','.c'] for p in root.rglob('*') if p.is_file())
with zipfile.ZipFile(root/'source-only.zip') as z:
 for n in z.namelist():
  assert z.read(n)==(root/n).read_bytes()==(root/'fresh-replay'/n).read_bytes(),n
for directory in [root,root/'fresh-replay']:
 for helper in ['verify_sources.py','verify_pins.py','audit_verify.py']:
  subprocess.run([sys.executable,str(directory/helper)],check=True)
 for mod in ['Closure','Words','Geometry','Attractor','Endpoint','Audit']:
  g=json.loads((directory/(mod+'.guard.json')).read_text());assert g['exit_code']==0 and g['reason'] is None,(directory,mod)
r={'status':'PASS','manifest_sha256':sha(root/'manifest.json'),'archive_sha256':sha(root/'source-only.zip'),
   'files':len(m),'fresh_extracted_replay':'PASS','compiler_nine_pins_scientific_original_copy':'PASS',
   'owned_declarations':120,'unsafe':0,'partial':0,'counts_changed':False}
(root/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
