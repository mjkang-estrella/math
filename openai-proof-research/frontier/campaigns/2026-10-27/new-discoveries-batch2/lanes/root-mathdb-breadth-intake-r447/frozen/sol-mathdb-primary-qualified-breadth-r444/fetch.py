from pathlib import Path
import urllib.request,urllib.error,json,re,hashlib,datetime
R=Path(__file__).resolve().parent;(R/'sources').mkdir(exist_ok=True);out=[]
for n in ['15578','15580','15957','16164','16627']:
 url='https://ems.press/journals/owr/articles/'+n
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read();status=f.status
  (R/'sources'/ (n+'.html')).write_bytes(b)
  links=re.findall(r'(?:href|content)="([^"]+\.pdf[^\"]*)"',b.decode())
  print(n,'pdf links',links)
  out.append({'url':url,'status':status,'file':'sources/'+n+'.html','sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
  if links:
   u=links[0]
   if u.startswith('/'):u='https://ems.press'+u
   with urllib.request.urlopen(u,timeout=25) as f:b=f.read();status=f.status
   (R/'sources'/(n+'.pdf')).write_bytes(b);out.append({'url':u,'status':status,'file':'sources/'+n+'.pdf','sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
 except Exception as e:
  out.append({'url':url,'failure':str(e)});print('FAIL',url,str(e))
  if isinstance(e,urllib.error.HTTPError) and e.code in [403,429]:break
(R/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
