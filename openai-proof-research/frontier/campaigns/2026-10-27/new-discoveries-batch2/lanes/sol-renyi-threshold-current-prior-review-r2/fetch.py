import pathlib,urllib.request,urllib.error,hashlib,json,datetime
L=pathlib.Path(__file__).resolve().parent
jobs=[('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'),('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD'),('li.pdf','https://arxiv.org/pdf/1704.02634'),('survey.pdf','https://arxiv.org/pdf/1604.04225')]
for name,url in jobs:
 row={'url':url,'name':name,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'bounded-public-math-review/1.0'}),timeout=35) as r:
   row.update(status=r.status,headers=dict(r.headers));b=r.read(12000001)
   if len(b)>12000000:raise ValueError('12MB response cap')
   (L/name).write_bytes(b);row.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:
  row['error']=repr(e)
  if isinstance(e,urllib.error.HTTPError):row.update(status=e.code,headers=dict(e.headers))
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps({k:v for k,v in row.items() if k!='headers'}),flush=True)
 if row.get('status') in (403,429):break
