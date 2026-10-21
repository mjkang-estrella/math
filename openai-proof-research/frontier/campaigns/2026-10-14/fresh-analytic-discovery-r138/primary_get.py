from pathlib import Path
import urllib.request,hashlib,json,tarfile,io,gzip,concurrent.futures
R=Path(__file__).resolve().parent
ids=['2109.07534v1','1601.02066v1','1108.3244v3','2312.16939v4']
def get(i):
 url='https://arxiv.org/src/'+i
 row={'id':i,'url':url,'read_extents':[]}
 try:
  b=urllib.request.urlopen(url,timeout=45).read(); folder=R/'private/primary'/i;folder.mkdir(parents=True,exist_ok=True)
  (folder/'raw.bin').write_bytes(b); row.update(size=len(b),sha256=hashlib.sha256(b).hexdigest(),local_path=str((folder/'raw.bin').relative_to(R)))
  files=[]
  try:
   with tarfile.open(fileobj=io.BytesIO(b),mode='r:*') as t:
    for m in t.getmembers():
     if not m.isfile() or m.name.startswith('/') or '..' in Path(m.name).parts or not m.name.endswith(('.tex','.bib')):continue
     data=t.extractfile(m).read(); p=folder/'text'/m.name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
     files.append({'path':str(p.relative_to(R)),'size':len(data),'sha256':hashlib.sha256(data).hexdigest(),'lines':len(data.splitlines())})
  except tarfile.ReadError:
   data=gzip.decompress(b) if b[:2]==b'\x1f\x8b' else b
   p=folder/'main.tex';p.write_bytes(data);files.append({'path':str(p.relative_to(R)),'size':len(data),'sha256':hashlib.sha256(data).hexdigest(),'lines':len(data.splitlines())})
  row['extracts']=files
 except Exception as e:row['failure']=repr(e)
 return row
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex: rows=list(ex.map(get,ids))
(R/'primary-ledger.json').write_text(json.dumps(rows,indent=2)+'\n')
for row in rows:
 print(row['id'],row.get('failure','ok'))
 for f in row.get('extracts',[]):print(f['path'],f['lines'])
