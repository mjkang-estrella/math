from pathlib import Path,PurePosixPath
import hashlib,json,shutil,zipfile,stat
D=Path.cwd(); B=D.parent
before=json.loads((D/'hashes/inputs-before.json').read_text())
for name,h in before.items():
 p=Path(name); assert hashlib.sha256(p.read_bytes()).hexdigest()==h
 rel=p.relative_to(B); q=D/'inputs'/rel; q.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(p,q)
z=D/'grid-formal-r6-source.zip'; shutil.copyfile(B/'grid-formal-r6'/z.name,z)
assert hashlib.sha256(z.read_bytes()).hexdigest()=='a4068de99037028f817f2f5d1652a97d7508c4419353da95abea04b45b977953'
out=D/'source-extraction'; 
if out.exists(): shutil.rmtree(out)
out.mkdir(exist_ok=False)
with zipfile.ZipFile(z) as f:
 seen=set(); total=0
 for x in f.infolist():
  p=PurePosixPath(x.filename)
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in x.filename
  assert p.as_posix() not in seen; seen.add(p.as_posix())
  assert not stat.S_ISLNK(x.external_attr>>16); total+=x.file_size; assert total<100_000_000
  target=out.joinpath(*p.parts); assert target.resolve().is_relative_to(out.resolve())
  if x.is_dir(): target.mkdir(parents=True,exist_ok=True)
  else: target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(f.read(x))
lean=list((out/'src').glob('*.lean')); assert len(lean)==47
(D/'receipts/safe-extraction.json').write_text(json.dumps({'sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'members':len(seen),'uncompressed_bytes':total,'lean_modules':len(lean),'paths_relative':True,'no_traversal_symlinks_duplicates':True,'lean_executed':False},indent=2)+'\n')
print('safe extraction',len(seen),'members;',len(lean),'Lean modules')
