from pathlib import Path,PurePosixPath
import json,hashlib,zipfile,stat
D=Path.cwd(); z=D/'grid-formal-r6-source.zip'; h=hashlib.sha256(z.read_bytes()).hexdigest()
assert h=='a4068de99037028f817f2f5d1652a97d7508c4419353da95abea04b45b977953'
out=D/'source-extraction';out.mkdir(exist_ok=False)
with zipfile.ZipFile(z) as f:
 seen=set();total=0
 for x in f.infolist():
  p=PurePosixPath(x.filename)
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in x.filename and ':' not in x.filename
  assert p.as_posix() not in seen;seen.add(p.as_posix())
  assert not stat.S_ISLNK(x.external_attr>>16)
  assert not stat.S_IFMT(x.external_attr>>16) or stat.S_ISREG(x.external_attr>>16) or stat.S_ISDIR(x.external_attr>>16)
  assert p.suffix not in ['.olean','.ilean','.so','.o','.a','.dll','.exe']
  total+=x.file_size;assert total<100_000_000
  target=out.joinpath(*p.parts);assert target.resolve().is_relative_to(out.resolve())
  if x.is_dir():target.mkdir(parents=True,exist_ok=True)
  else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(f.read(x))
 lean=list((out/'src').glob('*.lean'));assert len(lean)==47
(D/'receipts/safe-extraction.json').write_text(json.dumps({'sha256':h,'members':len(seen),'uncompressed_bytes':total,'lean_src_modules':len(lean),'all_paths_safe':True,'no_links_duplicates_or_compiled_artifacts':True,'lean_executed':False},indent=2)+'\n')
print('safe extraction:',len(seen),'members;',len(lean),'src modules; no Lean run')
