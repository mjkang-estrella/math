import urllib.request,json,pathlib,datetime,hashlib
L=pathlib.Path.cwd();rs=[]
for repo in ['openai/math','the-omega-institute/trureturing']:
 u=f'https://api.github.com/repos/{repo}/commits/HEAD'
 try:
  with urllib.request.urlopen(u,timeout=15) as f:b=f.read();status=f.status
  name=repo.split('/')[-1];(L/f'sources/{name}-HEAD.json').write_bytes(b);d=json.loads(b)
  rs.append(dict(url=u,status=status,sha256=hashlib.sha256(b).hexdigest(),head=d['sha'],utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 except Exception as e:rs.append(dict(url=u,error=str(e)))
print(json.dumps(rs,indent=2));(L/'outputs/registry.json').write_text(json.dumps(rs,indent=2))
