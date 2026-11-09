import urllib.request,tarfile,gzip,io,hashlib,json,sys
from pathlib import Path
r=Path(__file__).resolve().parent/'packet/private/primary'
r.mkdir(parents=True,exist_ok=True)
for ident in sys.argv[1:]:
 url='https://arxiv.org/src/'+ident
 dst=r/ident;dst.mkdir(exist_ok=True)
 try:
  with urllib.request.urlopen(url,timeout=40) as res:
   data=res.read(20000001);headers=dict(res.headers);final=res.url
  assert len(data)<=20000000
  (dst/'source-response.bin').write_bytes(data)
  out=[]
  try:
   archive=tarfile.open(fileobj=io.BytesIO(data),mode='r:*')
   for m in archive.getmembers():
    if not m.isfile():continue
    p=Path(m.name)
    assert not p.is_absolute() and '..' not in p.parts and m.size<20000000
    b=archive.extractfile(m).read();target=dst/'files'/p;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(b)
    out.append({'file':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
  except tarfile.ReadError:
   try:b=gzip.decompress(data)
   except gzip.BadGzipFile:b=data
   assert not b.startswith(b'%PDF')
   target=dst/'files/source.tex';target.parent.mkdir(exist_ok=True);target.write_bytes(b)
   out.append({'file':'source.tex','size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
  meta={'id':ident,'url':url,'final_url':final,'headers':headers,'response_sha256':hashlib.sha256(data).hexdigest(),'files':out,'reading':'retrieval only; no semantic credit'}
  (dst/'authentication.json').write_text(json.dumps(meta,indent=2))
  print(ident,json.dumps(out))
 except Exception as e:
  (dst/'access-failure.json').write_text(json.dumps({'url':url,'error':repr(e)}));print(ident,'FAIL',repr(e))
