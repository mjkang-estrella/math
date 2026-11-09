import pathlib,json,hashlib,urllib.request,datetime,subprocess
P=pathlib.Path(__file__).resolve().parent
out=[]
for aid in ['2301.05202','2303.04892','2211.16637','2211.01495','2301.09867','2210.17021']:
 url='https://arxiv.org/pdf/'+aid
 e={'url_requested':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'unversioned endpoint; version to be read from retained PDF'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-screen/1.0'}),timeout=18) as r:
   e.update(url_final=r.url,status=r.status);b=r.read(12000000)
  assert b.startswith(b'%PDF-') and len(b)<12000000
  p=P/(aid+'.pdf');p.write_bytes(b);e.update(path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest())
  # Persist binding before extraction.
  out.append(e);(P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  t=P/(aid+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True,timeout=20)
  b=t.read_bytes();e['derivative']={'path':t.name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 except Exception as ex:
  e['failure']=str(ex)
  if e not in out:out.append(e)
 (P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
 print(aid,e.get('failure','bound PDF and text'))
