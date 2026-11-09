from pathlib import Path
import urllib.request,urllib.error,json,re,hashlib,subprocess
R=Path(__file__).resolve().parent;(R/'primary').mkdir(exist_ok=True);logs=[]
for key,num in [('2014-40','13110'),('2014-51','13353'),('2015-13','13498'),('2015-17','13674'),('2014-36','13106')]:
 url='https://ems.press/journals/owr/articles/'+num
 try:
  with urllib.request.urlopen(url,timeout=25) as f: data=f.read();status=f.status
  (R/'primary'/ (key+'.html')).write_bytes(data)
  links=re.findall(r'(?:href|src)="([^"]+\.pdf[^" ]*)"',data.decode());print(key,links)
  logs.append({'url':url,'status':status,'file':'primary/'+key+'.html','links':links})
 except Exception as e:logs.append({'url':url,'error':str(e)});print(url,str(e))
(R/'downloads.json').write_text(json.dumps(logs,indent=2)+'\n')
