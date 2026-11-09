import urllib.request,urllib.error,pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).parent;P=L/'primary'
urls=[('miller-swanson-v1','https://arxiv.org/pdf/1206.1015v1')]
blocked=set()
for name,url in urls:
 host=urllib.parse.urlparse(url).netloc
 if host in blocked:continue
 meta={'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:
   b=r.read(12000000);meta.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  (P/(name+'.pdf')).write_bytes(b);meta.update(sha256=hashlib.sha256(b).hexdigest(),size=len(b))
 except Exception as e:
  meta['error']=str(e)
  if isinstance(e,urllib.error.HTTPError) and e.code in (403,429):blocked.add(host)
 (P/(name+'.meta.json')).write_text(json.dumps(meta,indent=2)+'\n');print(name,meta.get('status'),meta.get('error'),meta.get('size'))
