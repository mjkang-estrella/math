import pathlib,json,hashlib,urllib.request,urllib.error,subprocess,datetime
O=pathlib.Path(__file__).resolve().parent;out=[]
for a in ['2009.12802','2003.14361']:
 u='https://arxiv.org/pdf/'+a;e={'url':u,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  data=urllib.request.urlopen(u,timeout=15).read();p=O/'sources'/(a+'.pdf');p.write_bytes(data);e.update(path=str(p),size=len(data),sha256=hashlib.sha256(data).hexdigest());(O/'successor-provenance.json').write_text(json.dumps(out+[e],indent=2));subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as ex:
  e['failure']=repr(ex)
  if isinstance(ex,urllib.error.HTTPError) and ex.code in (403,429):out.append(e);break
 out.append(e)
(O/'successor-provenance.json').write_text(json.dumps(out,indent=2))
refs=[{'path':str(p),'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted((O/'sources').glob('*'))];(O/'source-bindings.json').write_text(json.dumps(refs,indent=2))
