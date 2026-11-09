import pathlib,json,hashlib,datetime,urllib.request,subprocess,resource,os
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
o=pathlib.Path(__file__).parent;(o/'sources').mkdir(exist_ok=True);receipts=[]
urls={'formal-conjectures-head':'https://api.github.com/repos/google-deepmind/formal-conjectures/commits/main'}
for name,url in urls.items():
 row={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'}),timeout=35) as r:
   data=r.read(20000000);row.update(status=r.status,final_url=r.url,headers=dict(r.headers),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));ext='pdf' if data.startswith(b'%PDF') else 'json';p=o/'sources'/f'{name}.{ext}';p.write_bytes(data)
   if ext=='pdf':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=20)
 except Exception as e:row['error']=str(e)
 receipts.append(row);(o/'formal-registry-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');print(name,row.get('status'),row.get('error'),flush=True)
