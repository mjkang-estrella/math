import pathlib,urllib.request,json,datetime,hashlib,subprocess,importlib.util
D=pathlib.Path(__file__).resolve().parents[1]
urls={'oddtown-successor':'https://arxiv.org/pdf/2302.05586','ribbon-refutation':'https://arxiv.org/pdf/2004.12564','layers-successor':'https://arxiv.org/pdf/2006.03799','openai-head':'https://api.github.com/repos/openai/math/commits/HEAD','omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','rowmotion-successor':'https://arxiv.org/pdf/2303.00451'}
r=[]
for name,url in urls.items():
 o={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-review/1.0'}),timeout=15) as f:b=f.read();o['status']=f.status
  p=D/'sources'/name;p.write_bytes(b);o.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if b[:4]==b'%PDF':subprocess.run(['pdftotext','-layout',str(p),str(p)+'.txt'],capture_output=True,timeout=12)
 except Exception as e:o['error']=str(e)
 r.append(o);print(o,flush=True)
(D/'sources/extra-receipts.json').write_text(json.dumps(r,indent=2)+'\n')
print({m:bool(importlib.util.find_spec(m)) for m in ['networkx','scipy','z3','sympy']})
