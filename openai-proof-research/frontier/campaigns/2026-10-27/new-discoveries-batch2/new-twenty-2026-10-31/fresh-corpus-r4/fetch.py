from pathlib import Path
import requests,json,hashlib,datetime
from concurrent.futures import ThreadPoolExecutor
p=Path(__file__).parent
urls={'spectral':'https://arxiv.org/html/1305.1139v1','partitions':'https://arxiv.org/html/1304.6563v1','hyperstar':'https://arxiv.org/html/1304.1315v3','cored':'https://www.polyu.edu.hk/ama/staff/new/qilq/LAA-HQS.pdf','openai-head':'https://api.github.com/repos/openai/math/commits/main','palomar-spectral':'https://data.palomar-registry.org/api/v1/results?q=spectral%20radii','palomar-partitions':'https://data.palomar-registry.org/api/v1/results?q=intersecting%20integer%20partitions','palomar-hyperstar':'https://data.palomar-registry.org/api/v1/results?q=hyperstar'}
def f(kv):
 k,u=kv; d=dict(key=k,url=u,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  r=requests.get(u,timeout=25);(p/(k+'.body')).write_bytes(r.content);d.update(status=r.status_code,final_url=r.url,sha256=hashlib.sha256(r.content).hexdigest(),bytes=len(r.content))
 except Exception as e:d['error']=str(e)
 return d
if __name__=='__main__':
 d=list(ThreadPoolExecutor(max_workers=2).map(f,urls.items()));(p/'source-receipts.json').write_text(json.dumps(d,indent=2));print(json.dumps(d,indent=2))
