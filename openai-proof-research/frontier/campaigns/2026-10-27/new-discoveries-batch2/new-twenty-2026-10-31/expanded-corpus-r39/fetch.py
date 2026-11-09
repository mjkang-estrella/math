import pathlib,requests,json,hashlib,datetime,subprocess,resource,os
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
w=pathlib.Path(__file__).resolve().parent;(w/'sources').mkdir(exist_ok=True);receipts=[]
urls={'openai-head':'https://api.github.com/repos/OpenAI/math/commits/HEAD','omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD',**{a:'https://arxiv.org/pdf/'+a for a in ['2006.06716','2007.13132','2007.07094','2006.02829','2007.09630','2008.06577','2008.09888','2007.14277','2008.09294']}}
for name,url in urls.items():
 rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
 try:
  r=requests.get(url,timeout=25);rec.update(status=r.status_code,final_url=r.url,sha256=hashlib.sha256(r.content).hexdigest(),bytes=len(r.content));p=w/'sources'/name;p.write_bytes(r.content)
  if r.status_code==200 and r.content.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p)+'.txt'],check=True,timeout=20)
  if name.endswith('head') and r.status_code==200:rec['head']=r.json()['sha']
 except Exception as e:rec['error']=str(e)
 receipts.append(rec);print(json.dumps(rec),flush=True);(w/'sources/receipts.json').write_text(json.dumps(receipts,indent=2))
