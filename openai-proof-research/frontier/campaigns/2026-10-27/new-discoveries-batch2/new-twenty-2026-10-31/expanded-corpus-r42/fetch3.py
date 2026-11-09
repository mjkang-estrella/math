import urllib.request,json,hashlib,pathlib,datetime,subprocess,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
resource.setrlimit(resource.RLIMIT_CPU,(100,100))
w=pathlib.Path(__file__).resolve().parent
(w/'sources').mkdir(exist_ok=True)
urls={"fejer-body":"https://www.rivmat.unipr.it/fulltext/2021-12-2/Riv_Parma_12-2-2021_07.pdf","complementation-public":"https://probxiv.com/problems/subgraph-complementation-and-minimum-rank"}
receipts=[]
for key,url in urls.items():
 r={"url":url,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={"User-Agent":"Research source verification"}),timeout=35) as f:
   data=f.read(); r.update(status=f.status,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),final_url=f.url)
   ext="pdf" if data.startswith(b"%PDF") else "html"; p=w/'sources'/(key+'.'+ext); p.write_bytes(data); r['file']=str(p)
   if ext=="pdf": subprocess.run(["pdftotext","-layout",str(p),str(p.with_suffix('.txt'))],check=True,timeout=30)
   else: pass
 except Exception as e:r['error']=str(e); r['status']=getattr(e,'code',None)
 receipts.append(r);print(json.dumps(r),flush=True)
 (w/'source-receipts-3.json').write_text(json.dumps(receipts,indent=2)+'\n')
