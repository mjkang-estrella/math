from pathlib import Path, PurePosixPath
import hashlib,json,zipfile,stat
L=Path(__file__).resolve().parent
P=L.parent
h=lambda b:hashlib.sha256(b).hexdigest()
r={}
z=P/'coxeter-normal-form-r3/330264-r3-FULL-LEAN.zip'
assert h(z.read_bytes())=='2cab69a4914f29fb3f934b8f57c8807bcb3298bea7e1b535246e9e205e3acaab'
r['330264_archive']=h(z.read_bytes())
print((P/'coxeter-normal-form-r3/packet-manifest.json').read_text()[:3000])
with zipfile.ZipFile(z) as a:
 for i in a.infolist():
  p=PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(i.external_attr>>16)
  assert not i.filename.endswith(('.olean','.ilean','.so'))
  if i.is_dir():continue
  dst=L/'original-330264'/p
  dst.parent.mkdir(parents=True,exist_ok=True)
  dst.write_bytes(a.read(i))
 r['330264_files']={i.filename:h(a.read(i)) for i in a.infolist() if not i.is_dir()}
manifest=json.loads((P/'conference-mds-resume-r4/MANIFEST.json').read_text())
r['324342_files']={}
with zipfile.ZipFile(L/'324342-frozen-snapshot.zip','w',zipfile.ZIP_DEFLATED) as a:
 for src,dst in [('lean/ConferenceMDS324342.lean','ConferenceMDS324342.lean'),('audit/Audit.lean','Audit.lean'),('audit/Controls.lean','Controls.lean')]:
  b=(P/'conference-mds-resume-r4'/src).read_bytes()
  assert h(b)==manifest['./'+src]
  r['324342_files'][dst]=h(b)
  a.writestr(dst,b)
with zipfile.ZipFile(L/'324342-frozen-snapshot.zip') as a:
 for i in a.infolist():
  p=PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(i.external_attr>>16)
  dst=L/'original-324342'/p
  dst.parent.mkdir(parents=True,exist_ok=True)
  dst.write_bytes(a.read(i))
(L/'input-verification.json').write_text(json.dumps(r,indent=2)+'\n')
