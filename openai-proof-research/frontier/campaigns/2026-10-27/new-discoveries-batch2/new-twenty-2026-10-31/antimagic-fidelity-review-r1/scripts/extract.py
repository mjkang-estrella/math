import zipfile, pathlib, hashlib, stat, json
L=pathlib.Path(__file__).resolve().parents[1]; A=L.parent/'antimagic-formal-r7a/source.zip'
h=hashlib.sha256(A.read_bytes()).hexdigest(); assert h=='987233b0343fb9855f659eefedaf28bc2a91576cf5c6c3a50342671895d3d175'
d=L/'fresh'; d.mkdir()
with zipfile.ZipFile(A) as z:
 for i in z.infolist():
  p=pathlib.PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename
  assert stat.S_IFMT(i.external_attr>>16) in (0,stat.S_IFREG,stat.S_IFDIR)
  assert not i.filename.endswith(('.olean','.ilean','.so'))
  assert i.file_size<20_000_000
 z.extractall(d)
mods=list(d.rglob('*.lean')); print('archive',h,'modules',len(mods))
(L/'evidence/input-before.json').write_text(json.dumps({str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [A,*mods]},indent=2))
