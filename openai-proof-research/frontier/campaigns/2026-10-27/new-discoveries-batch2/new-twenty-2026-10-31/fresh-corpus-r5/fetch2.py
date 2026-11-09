from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import requests,json,hashlib,datetime,subprocess
p=Path(__file__).parent
urls={'openai-current-tree':'https://api.github.com/repos/openai/math/git/trees/4eaee87548250b2682affda7d05d947c05554bae?recursive=1','palomar-domination':'https://data.palomar-registry.org/api/v1/results?q=domination','palomar-kostka':'https://data.palomar-registry.org/api/v1/results?q=Kostka','palomar-chromatic':'https://data.palomar-registry.org/api/v1/results?q=chromatic','gt-v1':'https://arxiv.org/pdf/1307.3999v1','squares':'https://arxiv.org/pdf/1311.1251','independent':'https://arxiv.org/pdf/1311.4147'}
def f(kv):
 k,u=kv;d={'name':k,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=requests.get(u,timeout=25);(p/(k+'.body')).write_bytes(r.content);d.update(status=r.status_code,final_url=r.url,sha256=hashlib.sha256(r.content).hexdigest(),bytes=len(r.content))
  if r.content.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p/(k+'.body')),str(p/(k+'.txt'))],check=True)
 except Exception as e:d['error']=str(e)
 return d
r=list(ThreadPoolExecutor(max_workers=2).map(f,urls.items()));(p/'receipts-2.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
