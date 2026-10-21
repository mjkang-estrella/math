from pathlib import Path
import urllib.request,hashlib,json,tarfile,io,gzip
R=Path(__file__).resolve().parent;D=R/'private/primary';D.mkdir(exist_ok=True)
ledger=[]
for id in ['2609.35574v1','2610.07577v1','2610.09640v1','2604.22366v2']:
 url='https://arxiv.org/src/'+id
 try:
  b=urllib.request.urlopen(url,timeout=45).read();(D/(id+'.raw')).write_bytes(b)
  files=[]
  try:
   with tarfile.open(fileobj=io.BytesIO(b),mode='r:*') as tar:
    for m in tar.getmembers():
     if not m.isfile() or not m.name.endswith(('.tex','.bib')):continue
     p=Path(m.name)
     if p.is_absolute() or '..' in p.parts:raise ValueError('unsafe member')
     data=tar.extractfile(m).read();out=D/id/p;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(data)
     files.append({'path':str(out.relative_to(R)),'member':m.name,'size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
  except tarfile.ReadError:
   data=gzip.decompress(b);out=D/id/'main.tex';out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(data);files=[{'path':str(out.relative_to(R)),'member':'single-gzip','size':len(data),'sha256':hashlib.sha256(data).hexdigest()}]
  ledger.append({'id':id,'url':url,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'files':files})
  print(id,len(files),flush=True)
 except Exception as e:ledger.append({'id':id,'url':url,'failure':repr(e)});print(id,repr(e),flush=True)
 (R/'primary-ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
