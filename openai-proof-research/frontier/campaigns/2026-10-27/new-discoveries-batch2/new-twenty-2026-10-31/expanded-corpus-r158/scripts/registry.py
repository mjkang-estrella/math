import urllib.request,pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1];rs=[]
urls=[('openai-head','https://api.github.com/repos/openai/math/commits/HEAD'),('omega-head','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'),('grid-publication','https://strathprints.strath.ac.uk/95696/')]
for name,url in urls:
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research evidence'}),timeout=20) as s:data=s.read();status=s.status
  (L/'sources'/name).write_bytes(data)
  rs.append(dict(name=name,url=url,status=status,sha256=hashlib.sha256(data).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 except Exception as e:rs.append(dict(name=name,url=url,error=str(e)))
(L/'outputs/registry-receipts.json').write_text(json.dumps(rs,indent=2));print(rs)
for name in ['openai','omega']:
 p=L/'sources'/f'{name}-head'
 if p.exists():print(name,json.loads(p.read_text())['sha'])
