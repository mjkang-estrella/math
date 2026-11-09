import urllib.request,urllib.error,pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).parent;P=L/'primary';P.mkdir(exist_ok=True)
urls=[('vision','https://aimpl.org/algvision/1/'),('rats9','https://aimpl.org/ratsubvarpos/9/'),('kstability','https://aimpl.org/kstability/3/')]
blocked=set()
for name,url in urls:
 host=urllib.parse.urlparse(url).netloc
 if host in blocked:continue
 meta={'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:
   b=r.read(10000000);meta.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  (P/(name+'.body')).write_bytes(b);meta.update(sha256=hashlib.sha256(b).hexdigest(),size=len(b))
 except Exception as e:
  meta.update(error=str(e));
  if isinstance(e,urllib.error.HTTPError) and e.code in (403,429):blocked.add(host)
 (P/(name+'.meta.json')).write_text(json.dumps(meta,indent=2)+'\n');print(name,meta.get('status'),meta.get('error'),meta.get('size'))
