import datetime,hashlib,json,pathlib,subprocess,urllib.request
ROOT=pathlib.Path(__file__).resolve().parents[3];OUT=ROOT/'frontier/sources/i13_fresh_discovery/literature'; OUT.mkdir(exist_ok=True)
sources=[('chen-liu-2026','https://arxiv.org/pdf/2610.06724'),('coregliano-razborov','https://arxiv.org/pdf/2108.06599'),('conlon-lee-blowups','https://arxiv.org/pdf/1809.01259'),('kifer-varadhan','https://arxiv.org/pdf/1012.2223'),('dobrushin-major','https://www.renyi.hu/~major/articles/non-central.pdf'),('breuer-major','https://www.renyi.hu/~major/articles/breuer.pdf')]
rows=[]
for key,url in sources:
 p=OUT/(key+'.pdf')
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'mathematical-research/1.0'})
  with urllib.request.urlopen(req,timeout=50) as r: b=r.read(); final=r.url
  assert b.startswith(b'%PDF'),(key,b[:30]);p.write_bytes(b)
  t=OUT/(key+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True)
  rows.append({'id':key,'url':url,'final_url':final,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'path':str(p.relative_to(ROOT)),'text_sha256':hashlib.sha256(t.read_bytes()).hexdigest()})
 except Exception as e: rows.append({'id':key,'url':url,'error':str(e)})
(OUT/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
