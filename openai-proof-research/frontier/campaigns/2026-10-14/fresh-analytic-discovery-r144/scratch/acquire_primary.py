from pathlib import Path,PurePosixPath
import urllib.request,hashlib,json,tarfile,io,gzip,concurrent.futures
r=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r144')
ids=['2602.03136v1','2610.08499v1','2509.02739v1','1705.06831v2']
def get(a):
 url='https://arxiv.org/src/'+a
 try:
  with urllib.request.urlopen(url,timeout=40) as h: b=h.read(); status=h.status; final=h.url
 except Exception as e: return {'id':a,'url':url,'failure':str(e)}
 p=r/'private/primary'/a;p.mkdir(parents=True,exist_ok=True);(p/'incoming.bin').write_bytes(b)
 record={'id':a,'url':url,'final_url':final,'status':status,'incoming_size':len(b),'incoming_sha256':hashlib.sha256(b).hexdigest(),'selected_members':[]}
 try:
  t=tarfile.open(fileobj=io.BytesIO(b)); members=[(m.name,t.extractfile(m).read()) for m in t.getmembers() if m.isfile() and m.name.endswith(('.tex','.bib','.bbl'))]
 except tarfile.ReadError:
  members=[('source.tex',gzip.decompress(b))]
 for name,data in members:
  path=PurePosixPath(name)
  if path.is_absolute() or '..' in path.parts: raise ValueError(name)
  q=p/'selected'/str(path);q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data)
  record['selected_members'].append({'name':name,'size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
 return record
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: rows=list(pool.map(get,ids))
(r/'PRIMARY-AUTH.json').write_text(json.dumps(rows,indent=2)+'\n')
for x in rows: print(x['id'], x.get('failure', [(z['name'],z['size']) for z in x.get('selected_members',[])]))
