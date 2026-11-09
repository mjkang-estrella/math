import os
os.sched_setaffinity(0,{0,1})
import urllib.request,json,pathlib,hashlib,datetime,resource,subprocess
resource.setrlimit(resource.RLIMIT_AS,(1200*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(90,90))
L=pathlib.Path(__file__).resolve().parent.parent
urls={x:'https://arxiv.org/pdf/'+x for x in ['2608.18392','2608.22816']}
receipts=[]
for name,url in urls.items():
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-review'}),timeout=25) as f:
   b=f.read(20*1024**2);r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  ext='json' if name=='registry-head' else 'pdf';p=L/'sources'/f'{name}.{ext}';p.write_bytes(b)
  if ext=='pdf':
   q=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True,text=True,timeout=20);r['pdftotext_exit']=q.returncode
 except Exception as e:r['error']=str(e)
 receipts.append(r);(L/'sources/final-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');print(r,flush=True)
