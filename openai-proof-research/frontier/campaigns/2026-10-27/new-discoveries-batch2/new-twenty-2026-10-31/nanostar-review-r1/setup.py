import pathlib,hashlib,json,zipfile,stat
here=pathlib.Path.cwd(); src=here.parent/'expanded-corpus-r162'
files=[p for p in src.rglob('*') if p.is_file() and not any(x in p.parts for x in ['.lake','replay','tmp','cache'])]
h={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}
(here/'inputs-before.json').write_text(json.dumps(h,indent=2))
with zipfile.ZipFile(src/'proof-source.zip') as z:
 for i in z.infolist():
  p=pathlib.PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(i.external_attr>>16)
  assert i.file_size < 10000000
  if i.is_dir(): continue
  out=here/'build'/p; out.parent.mkdir(parents=True,exist_ok=True); out.write_bytes(z.read(i))
 names=[i.filename for i in z.infolist()]
(here/'archive-inventory.json').write_text(json.dumps(names,indent=2))
print('hashed',len(h),'files; extracted safely')
