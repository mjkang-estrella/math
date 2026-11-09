from pathlib import Path
import urllib.request,urllib.error,json,hashlib,re,datetime
R=Path(__file__).resolve().parent;(R/'sources').mkdir(exist_ok=True);out=[]
for n in ['13684','13940','14604','14222','14226']:
 u='https://ems.press/journals/owr/articles/'+n
 try:
  with urllib.request.urlopen(u,timeout=25) as f:b=f.read();status=f.status
  p=R/'sources'/ (n+'.html');p.write_bytes(b)
  out.append({'url':u,'path':str(p.relative_to(R)),'status':status,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'date':datetime.datetime.now(datetime.timezone.utc).isoformat()})
  print(n,'PDF LINKS',re.findall(r'[^"\s<>]*\.pdf[^"\s<>]*',b.decode())[:15])
 except Exception as e:out.append({'url':u,'failure':str(e)});print(n,str(e))
(R/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
