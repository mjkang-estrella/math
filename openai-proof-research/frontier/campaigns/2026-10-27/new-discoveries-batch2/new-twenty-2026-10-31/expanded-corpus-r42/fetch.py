import urllib.request,json,hashlib,pathlib,datetime,subprocess,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
resource.setrlimit(resource.RLIMIT_CPU,(100,100))
w=pathlib.Path(__file__).resolve().parent
(w/'sources').mkdir(exist_ok=True)
urls={"openai-head":"https://api.github.com/repos/openai/math/commits/HEAD","omega-head":"https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD",**{i:"https://arxiv.org/pdf/"+i for i in ["2102.02979","2102.04126","2102.05352","2101.06180"]}}
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
 (w/'source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
