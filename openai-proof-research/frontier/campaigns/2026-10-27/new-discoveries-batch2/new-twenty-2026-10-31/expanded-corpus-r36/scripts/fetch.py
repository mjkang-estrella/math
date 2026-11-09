import urllib.request,json,pathlib,hashlib,datetime,resource,subprocess
resource.setrlimit(resource.RLIMIT_AS,(1200*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(90,90))
L=pathlib.Path(__file__).resolve().parent.parent
urls={'registry-head':'https://api.github.com/repos/OpenAI/math/commits/main','1908.03513':'https://arxiv.org/pdf/1908.03513','1908.05879':'https://arxiv.org/pdf/1908.05879','1910.13792':'https://arxiv.org/pdf/1910.13792','1908.06697':'https://arxiv.org/pdf/1908.06697','1911.06435':'https://arxiv.org/pdf/1911.06435','1912.01600':'https://arxiv.org/pdf/1912.01600'}
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
 receipts.append(r);(L/'sources/receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');print(r,flush=True)
