from pathlib import Path
import urllib.request,tarfile,io,hashlib,json
R=Path(__file__).resolve().parent
ledger=[]
for id in ['1603.06037v2','2606.01331v3','2608.13758v1']:
 url='https://arxiv.org/src/'+id
 try:
  b=urllib.request.urlopen(url,timeout=45).read(); d=R/'private/primary'/id;d.mkdir(parents=True,exist_ok=True);(d/'source.tar').write_bytes(b)
  row=dict(id=id,url=url,size=len(b),sha256=hashlib.sha256(b).hexdigest(),members=[])
  with tarfile.open(fileobj=io.BytesIO(b)) as tf:
   for m in tf.getmembers():
    if not m.isfile() or not m.name.endswith(('.tex','.bib')):continue
    p=Path(m.name)
    if p.is_absolute() or '..' in p.parts:raise ValueError('unsafe source member')
    z=tf.extractfile(m).read();dst=d/'extracted'/p;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(z)
    row['members'].append(dict(path=str(dst.relative_to(R)),size=len(z),sha256=hashlib.sha256(z).hexdigest()))
  ledger.append(row);print(id,[(x['path'],x['size']) for x in row['members']])
 except Exception as e:ledger.append(dict(id=id,url=url,error=str(e)));print(id,str(e))
(R/'primary-ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
