import pathlib,urllib.request,datetime,hashlib,json
D=pathlib.Path(__file__).resolve().parent;log=[]
for id in ['2308.06670','2306.08457','2401.11496','2407.07553','2408.03921']:
 u='https://arxiv.org/html/'+id+'v1';e={'url':u,'version':'v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=25) as r:b=r.read();e['http_status']=r.status
  p=D/(id+'.html');p.write_bytes(b);e.update(path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as ex:e['failure']=str(ex)
 log.append(e);(D/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
 print(e)
