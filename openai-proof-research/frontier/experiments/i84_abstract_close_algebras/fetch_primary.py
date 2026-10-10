"""Acquisition only. NOT called by the read-only verifier."""
from pathlib import Path
import urllib.request,urllib.error,datetime,json,hashlib,subprocess,concurrent.futures
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i84_abstract_close_algebras'; P=S/'primary'
items=[('cssww-v1.pdf','https://arxiv.org/pdf/0910.4953v1'),('rwi-v2.pdf','https://arxiv.org/pdf/1307.2598v2'),('haagerup.pdf','https://journals.msp.org/mscand/article/download/2067/2066')]
def fetch(item):
 name,url=item; d=dict(url=url,captured=datetime.datetime.now(datetime.timezone.utc).isoformat());q=P/name
 if q.exists():raise RuntimeError('No overwrites: '+str(q))
 try:
  try:r=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0 (research source verification)'}),timeout=35)
  except urllib.error.HTTPError as e:r=e
  with r:b=r.read();d.update(status=r.status,headers=dict(r.headers),final_url=r.url)
  q.write_bytes(b);d.update(local=str(q.relative_to(ROOT)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if b.startswith(b'%PDF'):
   z=subprocess.run(['pdftotext','-layout',str(q),'-'],capture_output=True);out=Path(str(q)+'.txt');out.write_bytes(z.stdout);d['extraction']=dict(local=str(out.relative_to(ROOT)),code=z.returncode,sha256=hashlib.sha256(z.stdout).hexdigest(),stderr=z.stderr.decode())
 except Exception as e:d['error']=repr(e)
 return d
if __name__=='__main__':
 with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:rows=list(ex.map(fetch,items))
 with (S/'primary-requests.jsonl').open('a') as f:
  for d in rows:f.write(json.dumps(d,sort_keys=True)+'\n')
 for d in rows:print(d.get('local',d['url']),d.get('status',d.get('error')))
