from pathlib import Path
import zipfile,hashlib,sys
p=Path(__file__).resolve().parent.parent
paths=[]
for d in ['src','scripts','controls']:
 paths.extend(f for f in (p/d).rglob('*') if f.is_file())
for n in ['TASK.txt','SUMMARY.md','PROOF.md','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md','VALIDATION.md','results.json','frozen-before.sha256','frozen-after.sha256','frozen-zip.sha256']:
 if (p/n).exists():paths.append(p/n)
z=p/'grid-formal-r4-source.zip'
with zipfile.ZipFile(z,'w',zipfile.ZIP_DEFLATED) as out:
 for f in sorted(paths):
  name=f.relative_to(p).as_posix()
  assert not name.startswith('/') and '..' not in Path(name).parts
  out.write(f,name)
(p/'source-zip.sha256').write_text(hashlib.sha256(z.read_bytes()).hexdigest()+'  '+z.name+'\n')
if len(sys.argv)>1:
 dest=p/sys.argv[1]
 dest.mkdir(exist_ok=False)
 with zipfile.ZipFile(z) as inp:
  for n in inp.namelist():
   assert not n.startswith('/') and '..' not in Path(n).parts
  inp.extractall(dest)
 for f in (dest/'scripts').glob('*.sh'):f.chmod(0o755)
print(z)
