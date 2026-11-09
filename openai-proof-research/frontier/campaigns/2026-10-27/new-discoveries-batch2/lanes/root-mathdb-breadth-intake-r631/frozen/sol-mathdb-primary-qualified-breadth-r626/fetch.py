from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime
D=Path(__file__).resolve().parent; out=[]
for ar in ['1201.3861v3','0912.2444v3']:
 url='https://arxiv.org/html/'+ar
 e={'url':url,'version':ar,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'headers':{'User-Agent':'Python-urllib/3','Accept':'text/html'}}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers=e['headers']),timeout=22) as r:
   b=r.read(); e['status']=r.status;e['final_url']=r.url
  (D/(ar+'.html')).write_bytes(b);e.update(sha256=hashlib.sha256(b).hexdigest(),size=len(b),path=ar+'.html')
 except Exception as x:e['failure']=str(x)
 out.append(e); print(e)
(D/'fetch-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
