from pathlib import Path
import urllib.request,hashlib,json,datetime
O=Path(__file__).resolve().parent
u='https://pmc.ncbi.nlm.nih.gov/articles/PMC536021/'
r={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'headers':{'User-Agent':'Mozilla/5.0','Accept':'text/html'}}
try:
 with urllib.request.urlopen(urllib.request.Request(u,headers=r['headers']),timeout=25) as f:b=f.read(8000000);r.update(status=f.status,final_url=f.url)
 (O/'burnside.html').write_bytes(b);r.update(path='burnside.html',size=len(b),sha256=hashlib.sha256(b).hexdigest())
except Exception as e:r.update(failure=str(e),retry=False)
(O/'fetch-provenance.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
