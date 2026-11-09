import pathlib,json,hashlib,urllib.request,datetime,subprocess
P=pathlib.Path(__file__).resolve().parent
out=[]
for a in ['2311.01208v1','2310.06192v1','2401.14301v1','2402.14661v1']:
 u='https://arxiv.org/pdf/'+a;e={'url':u,'version':a,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  req=urllib.request.Request(u,headers={'User-Agent':'Python-urllib/3'})
  with urllib.request.urlopen(req,timeout=25) as r:b=r.read(12000000);e['final_url']=r.url
  assert b.startswith(b'%PDF');p=P/(a+'.pdf');p.write_bytes(b);e.update({'pdf':p.name,'pdf_sha256':hashlib.sha256(b).hexdigest(),'pdf_size':len(b)})
  out.append(e);(P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  t=P/(a+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True)
  b=t.read_bytes();e.update({'text':t.name,'text_sha256':hashlib.sha256(b).hexdigest(),'text_size':len(b)})
 except Exception as ex:
  e['failure']=str(ex)
  if e not in out:out.append(e)
 (P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(a,e.get('failure','bound PDF and text'))
