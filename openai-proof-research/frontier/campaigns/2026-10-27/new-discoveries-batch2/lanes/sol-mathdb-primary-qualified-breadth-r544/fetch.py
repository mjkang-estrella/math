import pathlib,json,hashlib,urllib.request,datetime
D=pathlib.Path(__file__).resolve().parent
out=[]
for name,url in [('spectral','https://ems.press/journals/owr/articles/4080'),('hamilton','https://ems.press/journals/owr/articles/12861'),('tropical','https://ems.press/journals/owr/articles/15428')]:
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source screening'}),timeout=25) as r:
   b=r.read();status=r.status;final=r.url
  p=D/(name+'.html');p.write_bytes(b)
  out.append({'path':str(p),'url':url,'final_url':final,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':status,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'body_read':False})
 except Exception as e:
  out.append({'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'error':repr(e)})
(D/'source-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
