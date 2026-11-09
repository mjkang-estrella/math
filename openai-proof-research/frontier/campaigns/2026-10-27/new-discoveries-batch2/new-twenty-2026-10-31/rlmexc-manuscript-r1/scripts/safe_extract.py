import zipfile,pathlib,hashlib,json,stat
p=pathlib.Path('lean-source.zip'); h=hashlib.sha256(p.read_bytes()).hexdigest();assert h=='82262a7aa3f6548ebe9e15c3d8f0fef0feb120c5f0f45cc4a6e31eb6a3840a75'
dest=pathlib.Path('safe-extracted');dest.mkdir(exist_ok=True);rows=[]
with zipfile.ZipFile(p) as z:
 names=z.namelist();assert len(names)==len(set(names));assert sum(i.file_size for i in z.infolist())<20*1024**2
 for i in z.infolist():
  path=pathlib.PurePosixPath(i.filename)
  assert not path.is_absolute() and '..' not in path.parts and '\\' not in i.filename
  assert not stat.S_ISLNK(i.external_attr>>16)
  out=dest/path;assert out.resolve().is_relative_to(dest.resolve())
  if i.is_dir():out.mkdir(parents=True,exist_ok=True);continue
  data=z.read(i);out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(data)
  rows.append({'member':i.filename,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
mods=(dest/'module-order.txt').read_text().splitlines();assert len(mods)==9
pathlib.Path('receipts/safe-extraction.json').write_text(json.dumps({'status':'PASS','packet_sha256':h,'modules':mods,'members':rows,'executed_packet_code':False},indent=2)+'\n')
print('Safe extraction PASS;',len(rows),'files;',len(mods),'modules; no packet code executed')
