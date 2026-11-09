from pathlib import Path
import requests,datetime,hashlib,json,subprocess,resource,os
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
p=Path(__file__).parent;(p/'sources').mkdir(exist_ok=True)
urls={x:'https://arxiv.org/pdf/'+x for x in ['2205.05613','2206.07879','2206.13182','2206.12812','2205.14436','2205.07968','2206.04936','2207.02271']};urls.update({'openai-head':'https://api.github.com/repos/openai/math/commits/HEAD','omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'})
receipts=[]
for name,url in urls.items():
 try:
  r=requests.get(url,timeout=22);d=r.content; ext='.pdf' if d.startswith(b'%PDF') else '.json' if 'head' in name else '.response';f=p/'sources'/(name+ext);f.write_bytes(d);rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'status':r.status_code,'final_url':r.url,'file':str(f),'sha256':hashlib.sha256(d).hexdigest(),'bytes':len(d)}
  if ext=='.pdf': subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))],timeout=15,check=True)
 except Exception as e: rec={'url':url,'error':str(e),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 receipts.append(rec);(p/'source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');print(name,rec.get('status'),rec.get('bytes'),flush=True)
