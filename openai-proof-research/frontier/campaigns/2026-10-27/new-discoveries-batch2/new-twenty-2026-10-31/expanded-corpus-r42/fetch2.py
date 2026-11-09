import urllib.request,json,hashlib,pathlib,datetime,subprocess,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
resource.setrlimit(resource.RLIMIT_CPU,(100,100))
w=pathlib.Path(__file__).resolve().parent
(w/'sources').mkdir(exist_ok=True)
urls={"cheb-later":"https://arxiv.org/pdf/2305.03370","fejer-primary":"https://www.rivmat.unipr.it/vols/2021-12-2/07-alzer.pdf","partition-published":"https://dea.lib.unideb.hu/server/api/core/bitstreams/f8385f55-a1cd-4c30-a246-b1af22f31a92/content","omega-diff":"https://api.github.com/repos/the-omega-institute/trureturing/compare/66d225eda69544653f1ca0e66cf3aea530b1a2c6...bbae308affe6bde46be6cbdb01ec9efa8c47411f"}
receipts=[]
for key,url in urls.items():
 r={"url":url,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={"User-Agent":"Research source verification"}),timeout=35) as f:
   data=f.read(); r.update(status=f.status,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),final_url=f.url)
   ext="pdf" if data.startswith(b"%PDF") else "json"; p=w/'sources'/(key+'.'+ext); p.write_bytes(data); r['file']=str(p)
   if ext=="pdf": subprocess.run(["pdftotext","-layout",str(p),str(p.with_suffix('.txt'))],check=True,timeout=30)
   else: r['head']=json.loads(data).get('sha')
 except Exception as e:r['error']=str(e); r['status']=getattr(e,'code',None)
 receipts.append(r);print(json.dumps(r),flush=True)
 (w/'source-receipts-2.json').write_text(json.dumps(receipts,indent=2)+'\n')
