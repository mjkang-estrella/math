import urllib.request, pathlib, hashlib, json, datetime, subprocess, sys
L=pathlib.Path(__file__).resolve().parent
sources=[('official','https://arxiv.org/html/2510.09206v3'),('abstract','https://arxiv.org/abs/2510.09206'),('mt-abstract','https://arxiv.org/abs/2005.10930'),('anticonc','https://www.math.cmu.edu/~ttkocz/mypapers/mathematics/renyi-anti-conc.pdf')]
if len(sys.argv)>1:
 sources=[('anti-primary','https://arxiv.org/pdf/2406.04200'),('anti-abstract','https://arxiv.org/abs/2406.04200'),('mt-author','https://www.math.cmu.edu/users/ttkocz/mypapers/mathematics/renyi-discr-comp.pdf')]
with (L/('closest-receipts.jsonl' if len(sys.argv)>1 else 'live-receipts.jsonl')).open('w') as log:
 for name,url in sources:
  row=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
  try:
   req=urllib.request.Request(url,headers={'User-Agent':'Research review (public source verification)'})
   with urllib.request.urlopen(req,timeout=25) as r:
    row.update(status=r.status,final_url=r.url); h=hashlib.sha256(); count=0
    suffix='.pdf' if '/pdf/' in url or url.endswith('.pdf') else '.html'; path=L/(name+suffix)
    with path.open('wb') as f:
     while True:
      b=r.read(65536)
      if not b:break
      count+=len(b)
      if count>4000000: raise ValueError('4MB source cap exceeded')
      h.update(b);f.write(b)
    row.update(bytes=count,sha256=h.hexdigest(),file=path.name)
    if suffix=='.pdf':row['pdftotext_exit']=subprocess.run(['pdftotext','-layout',str(path),str(L/(name+'.txt'))]).returncode
  except Exception as e:row['error']=str(e)
  log.write(json.dumps(row)+'\n'); log.flush();print(json.dumps(row),flush=True)
