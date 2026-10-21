from pathlib import Path
import urllib.request,hashlib,tarfile,io,json,concurrent.futures,gzip
r=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r159/private/primary')
def one(item):
 name,url=item
 try:b=urllib.request.urlopen(url,timeout=45).read()
 except Exception as e:return dict(name=name,url=url,error=str(e))
 (r/(name+'.incoming')).write_bytes(b)
 a=dict(name=name,url=url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),selected=[])
 try:
  tf=tarfile.open(fileobj=io.BytesIO(b),mode='r:*')
  for m in tf.getmembers():
   if not m.isfile() or not m.name.endswith(('.tex','.bib')):continue
   p=Path(m.name)
   if p.is_absolute() or '..' in p.parts:raise RuntimeError('unsafe member')
   body=tf.extractfile(m).read();out=r/name/p;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(body)
   a['selected'].append(dict(member=m.name,bytes=len(body),sha256=hashlib.sha256(body).hexdigest(),lines=len(body.splitlines())))
 except tarfile.ReadError:
  try:body=gzip.decompress(b)
  except OSError:body=b
  out=r/(name+'.tex');out.write_bytes(body);a['selected'].append(dict(member='single-source',bytes=len(body),sha256=hashlib.sha256(body).hexdigest(),lines=len(body.splitlines())))
 return a
items=[('ghsy-v2','https://arxiv.org/src/1612.02873v2'),('zk-v2','https://arxiv.org/src/1504.04647v2')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:out=list(ex.map(one,items))
(r/'authentication.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
