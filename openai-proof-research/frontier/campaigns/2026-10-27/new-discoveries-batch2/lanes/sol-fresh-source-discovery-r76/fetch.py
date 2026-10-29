import urllib.request,datetime,hashlib,json
from pathlib import Path
P=Path(__file__).resolve().parent
items=[('source-arxiv.html','https://arxiv.org/abs/1901.10670'),('source-v1.pdf','https://arxiv.org/pdf/1901.10670v1'),('source-repository.pdf','https://repositorioaberto.uab.pt/server/api/core/bitstreams/43753f07-5603-4ed3-9492-02b5b85577b9/content'),('followup.html','https://arxiv.org/abs/2109.01172'),('followup-v1.pdf','https://arxiv.org/pdf/2109.01172v1'),('descartes-v1.pdf','https://arxiv.org/pdf/1307.6842v1'),('omega-descartes.lean','https://raw.githubusercontent.com/the-omega-institute/trureturing/70af54071bfd4ac098619a9db8c16bb6f7aced11/D5/S3/Analytic/ExponentialSum/DescartesRule.lean'),('geometry-mo.html','https://mathoverflow.net/questions/447678/convex-functions-in-convex-sets')]
records=[]
for name,url in items:
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'evidence/'+name}
 try:
  with urllib.request.urlopen(url,timeout=35) as f:
   b=f.read(8*1024*1024);r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
  (P/r['file']).write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if b'Just a moment' in b or b'captcha' in b[:3000].lower():r['challenge_stop']=True
 except Exception as e:r['error']=repr(e)
 records.append(r);(P/'fetch-records.json').write_text(json.dumps(records,indent=2)+'\n')
 print(name,r.get('status'),r.get('error'),flush=True)
