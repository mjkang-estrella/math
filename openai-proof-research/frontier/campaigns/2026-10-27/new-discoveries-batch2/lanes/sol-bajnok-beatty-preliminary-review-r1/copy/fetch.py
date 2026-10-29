import pathlib,urllib.request,hashlib,json,datetime,subprocess
P=pathlib.Path(__file__).resolve().parent
jobs=[('collatz','https://arxiv.org/pdf/2308.01181v2'),('bajnok','https://arxiv.org/pdf/2406.04045v1'),('bow','https://arxiv.org/pdf/2409.03859v1'),('collatz-vor','https://inmabb.criba.edu.ar/revuma/pdf/v69n1/v69n1a20.pdf'),('omega-head','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'),('openai-head','https://api.github.com/repos/openai/math/commits/HEAD')]
out=[]
for name,url in jobs:
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check'}),timeout=25) as f:b=f.read(8_000_000);r.update(status=f.status,final_url=f.url)
  ext='.pdf' if b.startswith(b'%PDF') else '.json';p=P/'sources'/(name+ext);p.write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if ext=='.pdf':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:r['error']=str(e)
 out.append(r)
(P/'http.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
