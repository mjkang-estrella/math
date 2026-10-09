from pathlib import Path
import requests,hashlib,json,datetime,subprocess,concurrent.futures
D=Path(__file__).resolve().parents[3]/'frontier/sources/i38_inequality_stability_discovery/literature'
items=[('fgl-v2.pdf','https://arxiv.org/pdf/2109.05984v2'),('hjn-v2.pdf','https://arxiv.org/pdf/1112.2993v2'),('kn-v2.pdf','https://arxiv.org/pdf/0807.4626v2'),('corthree-v3.pdf','https://arxiv.org/pdf/2306.03312v3')]
def fetch(item):
 name,url=item;o=dict(name=name,request=dict(method='GET',url=url),retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  r=requests.get(url,timeout=50);b=r.content;(D/name).write_bytes(b);o.update(status=r.status_code,final_url=r.url,headers=dict(r.headers),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),pdf=b.startswith(b'%PDF'))
  if o['pdf']:o['pdftotext_returncode']=subprocess.run(['pdftotext','-layout',str(D/name),str(D/name.replace('.pdf','.txt'))],capture_output=True).returncode
 except Exception as e:o['error']=repr(e)
 return o
out=list(concurrent.futures.ThreadPoolExecutor(max_workers=6).map(fetch,items));(D/'corrected-manifest.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps([{k:x.get(k) for k in ['name','status','bytes','pdf','error']} for x in out],indent=2))
