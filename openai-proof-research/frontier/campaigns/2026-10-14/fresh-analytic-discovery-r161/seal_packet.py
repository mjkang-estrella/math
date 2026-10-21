"""One-shot exact payload manifest. The three top-level envelopes are outside it."""
import hashlib,json,os,pathlib
R=pathlib.Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r161')
E={'FINAL.md','MANIFEST.json','REPORT.md'}
assert not (R/'MANIFEST.json').exists(),'Seal already exists; do not reseal.'
assert hashlib.sha256((R/'FROZEN-STATEMENT.md').read_bytes()).hexdigest()=='53f35f024803059dd77264ffc0f00d0c20209a3768e61551e8285eccaf7d5b38'
files=[]
def visit(d):
 for e in os.scandir(d):
  p=pathlib.Path(e.path);name=p.relative_to(R).as_posix()
  assert not e.is_symlink(),name
  if e.is_dir(follow_symlinks=False):visit(p)
  elif e.is_file(follow_symlinks=False):
   if name in E:continue
   b=p.read_bytes();files.append({'path':name,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
  else:raise ValueError(name)
visit(R);files.sort(key=lambda x:x['path'])
m={'format':'exact-selected-payload-v1','outside_envelopes':sorted(E),'files':files,'scope':'Artifact identity only; no mathematical gate; private copies retain original rights.'}
(R/'MANIFEST.json').write_text(json.dumps(m,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'payload_files':len(files),'payload_bytes':sum(x['bytes'] for x in files)},indent=2))
for name in ['FINAL.md','MANIFEST.json','REPORT.md']:
 print(name,hashlib.sha256((R/name).read_bytes()).hexdigest())
