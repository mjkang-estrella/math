import pathlib,hashlib,json,zipfile,datetime,stat
R=pathlib.Path(__file__).resolve().parent
P=R.parent
for d in ['scripts','receipts','logs','sources','outputs','fresh']:(R/d).mkdir(exist_ok=True)
m={}
for lane in ['expanded-corpus-r73','collapsing-review-r1']:
 for f in sorted((P/lane).rglob('*')):
  if f.is_file():m[str(f.relative_to(P))]=hashlib.sha256(f.read_bytes()).hexdigest()
(R/'receipts/before.json').write_text(json.dumps({'utc':str(datetime.datetime.now(datetime.timezone.utc)),'hashes':m},indent=2))
z=P/'expanded-corpus-r73/lean-packet/source-only-packet.zip'
with zipfile.ZipFile(z) as a:
 for i in a.infolist():
  p=pathlib.PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(i.external_attr>>16)
  assert p.suffix not in ['.olean','.ilean','.so']
  assert i.file_size<10000000
 a.extractall(R/'fresh')
(R/'receipts/zip.sha256').write_text(hashlib.sha256(z.read_bytes()).hexdigest())
