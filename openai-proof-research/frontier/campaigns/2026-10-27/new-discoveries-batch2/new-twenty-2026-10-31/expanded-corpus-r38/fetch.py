from pathlib import Path
import requests,json,hashlib,datetime,subprocess
H=Path(__file__).resolve().parent; (H/'sources').mkdir(exist_ok=True)
items=[('openai-head','https://api.github.com/repos/OpenAI/math/commits/HEAD'),('omega-repo','https://api.github.com/repos/the-omega-institute/trureturing'),('omega-head','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'),('sorting','https://dmtcs.episciences.org/7411/pdf'),('gerzon','https://arxiv.org/pdf/2004.02240'),('bicyclic','https://arxiv.org/pdf/2005.02141'),('borel','https://arxiv.org/pdf/2004.02162')]
receipts=[]
for name,url in items:
 try:
  r=requests.get(url,timeout=35); data=r.content; suffix='.pdf' if data.startswith(b'%PDF') else '.json' if 'github' in url else '.html';p=H/'sources'/(name+suffix);p.write_bytes(data)
  e={'name':name,'url':url,'final_url':r.url,'status':r.status_code,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'file':str(p.relative_to(H))};receipts.append(e);print(e,flush=True)
  if suffix=='.pdf': subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:receipts.append({'name':name,'url':url,'error':str(e)});print(e,flush=True)
(H/'fetch-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
