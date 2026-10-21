from pathlib import Path,PurePosixPath
import urllib.request,tarfile,io,json,hashlib,concurrent.futures
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/fresh-analytic-discovery-r140');(R/'private/primary').mkdir(exist_ok=True)
def get(key):
 url='https://arxiv.org/src/'+key
 try:b=urllib.request.urlopen(url,timeout=45).read()
 except Exception as e:return {'id':key,'url':url,'error':str(e)}
 raw=R/'private/primary'/f'{key}.tar';raw.write_bytes(b); rec={'id':key,'url':url,'raw':str(raw.relative_to(R)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'members':[]}
 try:
  with tarfile.open(fileobj=io.BytesIO(b)) as tar:
   for m in tar.getmembers():
    q=PurePosixPath(m.name)
    if not m.isfile() or q.is_absolute() or '..' in q.parts or q.suffix not in ['.tex','.bib']: continue
    data=tar.extractfile(m).read();f=R/'private/primary'/key/str(q);f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(data);rec['members'].append({'path':str(f.relative_to(R)),'size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
 except Exception as e:rec['error']=str(e)
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool: recs=list(pool.map(get,['1907.11966v3','1612.07304v3','1701.03015v2']))
(R/'primary-authentication.json').write_text(json.dumps(recs,indent=2));print(json.dumps(recs,indent=2))
