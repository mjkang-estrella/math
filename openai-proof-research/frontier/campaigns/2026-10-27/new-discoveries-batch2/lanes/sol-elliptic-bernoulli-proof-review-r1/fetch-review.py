import urllib.request,json,hashlib,datetime,concurrent.futures
from pathlib import Path
out=Path(__file__).parent/'new-sources';out.mkdir(exist_ok=True)
jobs={
'omega-dev':'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/dev',
'omega-main':'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/main',
'openai':'https://api.github.com/repos/openai/math/commits/main',
'aim':'https://api.github.com/repos/MColbrook/AIM/commits/main',
'count':'https://api.github.com/repos/suvrit/count-ex-machina/git/trees/main',
'figshare-metadata':'https://api.figshare.com/v2/articles/9383633',
'dlmf-addition':'https://dlmf.nist.gov/23.10',
'dlmf-periods':'https://dlmf.nist.gov/23.2',
'dlmf-fourier':'https://dlmf.nist.gov/23.8'}
def get(k,u):
 r={'name':k,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical-source-review/1.0'}),timeout=20) as f:
   d=f.read(3_000_001)
   if len(d)>3_000_000:raise ValueError('3MB cap')
   (out/(k+'.body')).write_bytes(d);r.update(status=f.status,bytes=len(d),sha256=hashlib.sha256(d).hexdigest(),final_url=f.url)
   try:r['head']=json.loads(d).get('sha')
   except Exception:pass
 except Exception as e:r['failure']=str(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:rows=list(ex.map(lambda x:get(*x),jobs.items()))
(out/'http.json').write_text(json.dumps(rows,indent=2))
for r in rows:print(r['name'],r.get('head') or r.get('status') or r.get('failure'))
