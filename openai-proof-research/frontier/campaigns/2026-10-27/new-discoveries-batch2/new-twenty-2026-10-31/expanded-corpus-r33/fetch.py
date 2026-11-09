import requests,pathlib,json,hashlib,datetime,subprocess,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100))
o=pathlib.Path(__file__).resolve().parent;(o/'sources').mkdir(exist_ok=True)
urls={'registry-head':'https://api.github.com/repos/openai/math/commits/main','matrix':'https://arxiv.org/pdf/1811.09981','matrix-later':'https://arxiv.org/pdf/2210.12405','roots':'https://arxiv.org/pdf/1812.09775','frames-v1':'https://arxiv.org/pdf/1901.06096v1','frames-v3':'https://arxiv.org/pdf/1901.06096v3'}
receipts=[]
for name,url in urls.items():
 try:
  r=requests.get(url,timeout=35);d=r.content;ext='pdf' if d.startswith(b'%PDF') else 'json' if name=='registry-head' else 'html';p=o/'sources'/f'{name}.{ext}';p.write_bytes(d);rec={'name':name,'url':url,'final_url':r.url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':r.status_code,'sha256':hashlib.sha256(d).hexdigest(),'bytes':len(d),'file':str(p)}
  if ext=='pdf':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=15)
 except Exception as e:rec={'name':name,'url':url,'error':str(e)}
 receipts.append(rec);print(rec,flush=True)
(o/'source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
