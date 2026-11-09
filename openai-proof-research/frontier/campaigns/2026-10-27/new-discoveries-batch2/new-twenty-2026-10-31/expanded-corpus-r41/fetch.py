import pathlib,requests,json,hashlib,datetime,subprocess,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
p=pathlib.Path(__file__).resolve().parent;(p/'sources').mkdir(exist_ok=True)
urls={'openai-head':'https://api.github.com/repos/OpenAI/math/commits/HEAD','omega-head':'https://api.github.com/repos/teorth/analysis/commits/HEAD'}
for a in ['2010.11112','2011.14502','2012.07409','2011.01892','2012.11162','2012.11177','2011.11187','2012.09901'] : urls[a]='https://arxiv.org/pdf/'+a
for name,url in urls.items():
 receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
 try:
  r=requests.get(url,timeout=25);b=r.content;receipt.update(status=r.status_code,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(p/'sources'/f'{name}.response').write_bytes(b)
  if b.startswith(b'%PDF'):
   (p/'sources'/f'{name}.pdf').write_bytes(b);subprocess.run(['pdftotext','-layout',str(p/'sources'/f'{name}.pdf'),str(p/'sources'/f'{name}.txt')],timeout=20,check=True)
 except Exception as e: receipt['error']=str(e)
 (p/'sources'/f'{name}.receipt.json').write_text(json.dumps(receipt,indent=2));print(name,receipt,flush=True)
