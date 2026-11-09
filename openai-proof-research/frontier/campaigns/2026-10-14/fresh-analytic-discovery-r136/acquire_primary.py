from pathlib import Path
import urllib.request,hashlib,json,tarfile,io,gzip,concurrent.futures
R=Path(__file__).resolve().parent
ids=['1510.01260v2','1701.06943v2']
def one(id):
 url='https://arxiv.org/src/'+id
 try:
  b=urllib.request.urlopen(url,timeout=45).read(); p=R/'private/primary'/id;p.mkdir(exist_ok=True);(p/'source.download').write_bytes(b)
  rows=[]
  try:
   t=tarfile.open(fileobj=io.BytesIO(b),mode='r:*')
   for m in t.getmembers():
    if not m.isfile() or not m.name.endswith(('.tex','.bib')):continue
    q=p/Path(m.name).name;d=t.extractfile(m).read();q.write_bytes(d);rows.append(dict(path=str(q.relative_to(R)),size=len(d),sha256=hashlib.sha256(d).hexdigest()))
  except tarfile.ReadError:
   d=gzip.decompress(b) if b[:2]==b'\x1f\x8b' else b;(p/'main.tex').write_bytes(d);rows.append(dict(path=str((p/'main.tex').relative_to(R)),size=len(d),sha256=hashlib.sha256(d).hexdigest()))
  return dict(id=id,url=url,size=len(b),sha256=hashlib.sha256(b).hexdigest(),files=rows)
 except Exception as e:return dict(id=id,url=url,error=str(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:rows=list(ex.map(one,ids))
(R/'primary-ledger.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
