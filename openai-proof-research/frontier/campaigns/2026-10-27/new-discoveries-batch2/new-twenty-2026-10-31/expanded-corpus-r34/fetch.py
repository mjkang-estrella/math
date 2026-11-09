import urllib.request,hashlib,json,datetime,pathlib,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
L=pathlib.Path(__file__).resolve().parent;(L/'sources').mkdir(exist_ok=True)
urls={'registry-head':'https://api.github.com/repos/openai/math/commits/main','dominator':'https://arxiv.org/pdf/1904.06293','irredundance':'https://arxiv.org/pdf/1904.02595','determinant':'https://arxiv.org/pdf/1902.09644','forcing':'https://arxiv.org/pdf/1903.08614','cycles':'https://arxiv.org/pdf/1902.08133'}
receipts=[]
for name,url in urls.items():
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source review'}),timeout=25) as f:
   data=f.read(15000000); r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)); (L/'sources'/(name+('.json' if name=='registry-head' else '.pdf'))).write_bytes(data)
 except Exception as e:r['error']=str(e)
 receipts.append(r);print(r,flush=True)
 (L/'fetch-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
