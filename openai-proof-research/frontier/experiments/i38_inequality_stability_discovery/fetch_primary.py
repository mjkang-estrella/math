from pathlib import Path
import requests,hashlib,json,datetime,subprocess,concurrent.futures
ROOT=Path(__file__).resolve().parents[3]; S=ROOT/'frontier/sources/i38_inequality_stability_discovery'; D=S/'literature';D.mkdir(exist_ok=True)
requests_list=[('hjn-author.pdf','https://web.math.princeton.edu/~naor/homepage%20files/PropR3.pdf'),('kn-author.pdf','https://web.math.princeton.edu/~naor/homepage%20files/kernel.pdf'),('kim-current.html','https://arxiv.org/abs/1212.2544'),('kim-v1.pdf','https://arxiv.org/pdf/1212.2544v1'),('fgl-current.html','https://arxiv.org/abs/2109.05984'),('fgl-published.pdf','https://preprint.press.jhu.edu/ajm/sites/default/files/AJM-frank-gontier-lewin-FINAL.pdf'),('kn-current.html','https://arxiv.org/abs/0807.4626'),('hyperstable-current.html','https://arxiv.org/abs/2209.11216'),('hyperstable-v1.pdf','https://arxiv.org/pdf/2209.11216v1')]
def fetch(item):
 name,url=item;out={'name':name,'request':{'method':'GET','url':url},'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=requests.get(url,timeout=50); b=r.content;(D/name).write_bytes(b);out.update(status=r.status_code,final_url=r.url,headers=dict(r.headers),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),pdf=b.startswith(b'%PDF'))
  if out['pdf']:
   p=subprocess.run(['pdftotext','-layout',str(D/name),str(D/name.replace('.pdf','.txt'))],capture_output=True,text=True);out['pdftotext_returncode']=p.returncode
 except Exception as e:out['error']=repr(e)
 return out
results=list(concurrent.futures.ThreadPoolExecutor(max_workers=6).map(fetch,requests_list));(D/'manifest.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps([{k:x.get(k) for k in ['name','status','bytes','pdf','error']} for x in results],indent=2))
