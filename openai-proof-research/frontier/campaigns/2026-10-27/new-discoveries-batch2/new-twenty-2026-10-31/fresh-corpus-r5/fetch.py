from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import requests,json,hashlib,datetime,subprocess
p=Path(__file__).parent
urls={'gt':'https://arxiv.org/pdf/1307.3999','majority':'https://arxiv.org/pdf/1311.0479','orbital':'https://arxiv.org/pdf/1310.3792','palomar-majority':'https://data.palomar-registry.org/api/v1/results?q=majority%20out-dominating','palomar-orbital':'https://data.palomar-registry.org/api/v1/results?q=orbital%20chromatic','palomar-gt':'https://data.palomar-registry.org/api/v1/results?q=Gelfand%20Tsetlin','openai-head':'https://api.github.com/repos/openai/math/commits/main','mathdb-majority':'https://mathdb.com/p/326640'}
def f(kv):
 k,u=kv;d={'name':k,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=requests.get(u,timeout=25);(p/(k+'.body')).write_bytes(r.content);d.update(status=r.status_code,final_url=r.url,sha256=hashlib.sha256(r.content).hexdigest(),bytes=len(r.content))
  if r.content.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p/(k+'.body')),str(p/(k+'.txt'))],check=True)
 except Exception as e:d['error']=str(e)
 return d
r=list(ThreadPoolExecutor(max_workers=2).map(f,urls.items()));(p/'receipts.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
