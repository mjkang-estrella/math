import urllib.request,pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1]; out=[]
for name,url in [('path-prior','https://arxiv.org/pdf/2405.15897'),('turan-prior','https://arxiv.org/pdf/2507.13267'),('partial-companion','https://arxiv.org/pdf/2204.08010'),('trees-prior','https://arxiv.org/abs/2509.13029'),('omega-tree','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/1764a0c7f33be6acf6dcaf4ad4007da021469ae9?recursive=1')]:
 try:
  with urllib.request.urlopen(url,timeout=15) as h: data=h.read(); status=h.status
  (L/('sources/'+name+('.pdf' if '/pdf/' in url else '.json'))).write_bytes(data);out.append(dict(url=url,status=status,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 except Exception as e:out.append(dict(url=url,error=str(e)))
(L/'outputs/more-http.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
