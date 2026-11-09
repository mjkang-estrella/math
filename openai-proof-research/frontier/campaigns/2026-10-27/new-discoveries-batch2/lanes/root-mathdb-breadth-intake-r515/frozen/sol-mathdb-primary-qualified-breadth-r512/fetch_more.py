import pathlib,json,hashlib,urllib.request,datetime,subprocess
P=pathlib.Path(__file__).resolve().parent;out=json.loads((P/'source-provenance.json').read_text())
for name,url in [('LEsurvey11','https://www.math.ucla.edu/~pak/papers/LEsurvey11.pdf'),('2210.17021v1','https://arxiv.org/pdf/2210.17021v1')]:
 e={'url_requested':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=20) as r:e.update(status=r.status,url_final=r.url);b=r.read(12000000)
  assert b.startswith(b'%PDF-') and len(b)<12000000
  p=P/(name+'.pdf');p.write_bytes(b);e.update(path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest());out.append(e)
  (P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  t=P/(name+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True,timeout=20)
  b=t.read_bytes();e['derivative']={'path':t.name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 except Exception as ex:
  e['failure']=str(ex)
  if e not in out:out.append(e)
 (P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(name,e.get('failure','bound'))
