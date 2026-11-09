from pathlib import Path
import hashlib,zipfile,json
lane=Path(__file__).resolve().parent.parent
frozen=json.loads((lane/'frozen-before.json').read_text())
assert all(hashlib.sha256((lane/'src'/n).read_bytes()).hexdigest()==h for n,h in frozen.items())
paths=[]
for d in ['src','scripts','controls']:
 paths.extend(p for p in (lane/d).rglob('*') if p.is_file() and '__pycache__' not in p.parts)
paths.extend(lane/n for n in ['TASK.txt','SUMMARY.md','PROOF.md','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md','results.json','frozen-before.json','frozen-after.json'])
z=lane/'grid-formal-r2-source.zip'
with zipfile.ZipFile(z,'w',zipfile.ZIP_DEFLATED) as f:
 for p in sorted(paths):
  name=p.relative_to(lane).as_posix();assert not name.startswith('/') and '..' not in Path(name).parts
  f.write(p,name)
(lane/'source-zip.sha256').write_text(hashlib.sha256(z.read_bytes()).hexdigest()+'  '+z.name+'\n')
verify=lane/'verification';verify.mkdir(exist_ok=False)
with zipfile.ZipFile(z) as f:
 for name in f.namelist():
  assert not name.startswith('/') and '..' not in Path(name).parts
 f.extractall(verify)
(verify/'scripts/lean.sh').chmod(0o755)
print(z.name, 'files',len(paths),'fresh', verify)
