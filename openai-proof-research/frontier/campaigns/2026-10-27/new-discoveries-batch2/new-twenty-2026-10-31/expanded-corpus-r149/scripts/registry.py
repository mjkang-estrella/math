import urllib.request,json,hashlib,pathlib,datetime
L=pathlib.Path(__file__).resolve().parents[1]
for repo in ['openai/math','the-omega-institute/trureturing']:
 u=f'https://api.github.com/repos/{repo}/commits/HEAD'
 try:
  with urllib.request.urlopen(u,timeout=20) as f:b=f.read();s=f.status
  d=json.loads(b);(L/('sources/'+repo.split('/')[0]+'-HEAD.json')).write_bytes(b)
  print(json.dumps(dict(url=u,status=s,head=d['sha'],sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat())))
 except Exception as e:print(u,str(e))
