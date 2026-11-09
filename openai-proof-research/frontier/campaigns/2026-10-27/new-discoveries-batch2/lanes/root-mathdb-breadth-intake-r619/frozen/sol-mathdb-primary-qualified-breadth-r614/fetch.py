import urllib.request,json,hashlib,datetime
from pathlib import Path
L=Path(__file__).parent;out=[]
for a in ['2510.00251','2510.02008','2601.03891']:
 u='https://arxiv.org/html/'+a+'v1';r={'url':u,'version':'v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'headers':{'User-Agent':'Research/1.0','Accept':'text/html'}}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers=r['headers']),timeout=18) as f:b=f.read(6000000);r['final_url']=f.url
  p=L/(a+'.html');p.write_bytes(b);r.update(path=p.name,sha256=hashlib.sha256(b).hexdigest(),size=len(b),status='fetched_bound_before_extraction')
 except Exception as e:r.update(status='HOLD_ACCESS',error=str(e))
 out.append(r)
(L/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
