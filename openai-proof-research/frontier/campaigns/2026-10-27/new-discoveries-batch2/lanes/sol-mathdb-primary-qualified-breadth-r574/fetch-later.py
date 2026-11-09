import pathlib,json,hashlib,urllib.request,datetime
P=pathlib.Path(__file__).resolve().parent
log=json.loads((P/'source-provenance.json').read_text())
for name,arx in [('farey-v3','1607.03414'),('hyperbolic-v3','2212.09037')]:
 url='https://arxiv.org/html/'+arx+'v3';now=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(url,timeout=35) as r:b=r.read();status=r.status;final=r.url
  p=P/(name+'.html');p.write_bytes(b)
  log.append({'name':name,'url':url,'version':'v3','utc':now,'http':status,'final_url':final,'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'coverage':'bytes bound; unread'})
 except Exception as e:log.append({'name':name,'url':url,'utc':now,'error':str(e),'retry':False})
(P/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n');print(json.dumps(log,indent=2))
