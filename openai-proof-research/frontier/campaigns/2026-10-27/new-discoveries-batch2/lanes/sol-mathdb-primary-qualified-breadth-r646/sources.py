import pathlib,urllib.request,json,hashlib,datetime
O=pathlib.Path(__file__).resolve().parent
log=[]
for a in ['1961','1973','2040','1795']:
 u='https://ems.press/journals/owr/articles/'+a
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Python-urllib/3'}),timeout=25) as r:b=r.read();final=r.url
  p=O/('ems'+a+'.html');p.write_bytes(b);log.append({'url':u,'final_url':final,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':p.name,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'coverage':'bytes bound; not yet read'})
 except Exception as e:
  log.append({'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'error':str(e),'retry':False})
(O/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
print(json.dumps(log,indent=2))
