import pathlib,zipfile,stat,hashlib,json
L=pathlib.Path(__file__).parent;B=L.parent
def extract(src,d):
 d.mkdir()
 with zipfile.ZipFile(src) as z:
  assert sum(x.file_size for x in z.infolist())<100*1024*1024
  for x in z.infolist():
   p=pathlib.PurePosixPath(x.filename)
   assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(x.external_attr>>16)
   assert (x.external_attr>>16)&0o170000 in [0,0o100000,0o040000]
   if x.is_dir(): (d/p).mkdir(parents=True,exist_ok=True);continue
   assert not x.filename.endswith(('.olean','.so','.ilean'))
   (d/p).parent.mkdir(parents=True,exist_ok=True);(d/p).write_bytes(z.read(x))
extract(B/'coxeter-normal-form-r3/330264-r3-FULL-LEAN.zip',L/'replay-330264')
# r4 is an unpacked packet: freeze the exact main/audit sources into a review-owned zip, then safe-extract.
with zipfile.ZipFile(L/'conference-source-snapshot.zip','w') as z:
 for f in ['lean/ConferenceMDS324342.lean','audit/Audit.lean','audit/Controls.lean']:
  z.writestr(pathlib.Path(f).name,(B/'conference-mds-resume-r4'/f).read_bytes())
extract(L/'conference-source-snapshot.zip',L/'replay-324342')
corpus=B.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
hits=[]
for f in sorted(corpus.glob('mathdb-normalized-chunk-*.jsonl')):
 data=f.read_bytes()
 for n,line in enumerate(data.splitlines(keepends=True),1):
  if any(('"mathdb_id": '+i).encode() in line or ('"mathdb_id":'+i).encode() in line for i in ['330264','352038','324342']):
   r=json.loads(line)
   if str(r.get('id',r.get('mathdb_id'))) not in ['330264','352038','324342']:continue
   i=str(r.get('id',r.get('mathdb_id')))
   (L/(i+'.raw.jsonl')).write_bytes(line)
   hits.append(dict(id=i,path=str(f),line=n,chunk_sha256=hashlib.sha256(data).hexdigest(),line_sha256=hashlib.sha256(line).hexdigest(),record=r))
(L/'literal-bindings.json').write_text(json.dumps(hits,indent=2))
print('literal matches',[(r['id'],r['line']) for r in hits])
