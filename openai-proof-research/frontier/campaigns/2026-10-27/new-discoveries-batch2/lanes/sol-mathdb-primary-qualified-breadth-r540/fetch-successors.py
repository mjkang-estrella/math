import pathlib,urllib.request,datetime,json,hashlib
P=pathlib.Path(__file__).resolve().parent;out=json.loads((P/'download-bindings.json').read_text())
for ident in ['2608.02085v1','2301.13557v3','1310.8461v1']:
 url='https://arxiv.org/html/'+ident;n=ident.replace('/','_')+'.html'
 try:
  with urllib.request.urlopen(url,timeout=35) as r:b=r.read();status=r.status
  (P/n).write_bytes(b);out.append({'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':n,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'status':status})
 except Exception as e:out.append({'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'error':str(e),'retry':False})
(P/'download-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
