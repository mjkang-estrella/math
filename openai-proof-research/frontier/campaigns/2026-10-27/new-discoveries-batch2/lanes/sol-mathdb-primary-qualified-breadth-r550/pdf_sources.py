from pathlib import Path
import re,json,hashlib,urllib.request,datetime,subprocess
D=Path(__file__).parent;out=[]
for a in ['1054','4330','17469','3389']:
 h=(D/(a+'.html')).read_text();u=re.search(r'https[^"<> ]+\.pdf',h).group().rstrip('\\')
 try:
  with urllib.request.urlopen(u,timeout=25) as r:b=r.read()
  assert b.startswith(b'%PDF');p=D/(a+'.pdf');p.write_bytes(b)
  out.append(dict(url=u,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest()))
 except Exception as e:
  out.append(dict(url=u,error=str(e)));break
(D/'pdf-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
for e in out:
 if 'error' not in e:subprocess.run(['pdftotext','-layout',str(D/e['path']),str(D/(Path(e['path']).stem+'.txt'))],check=True)
t=[]
for e in out:
 if 'error' not in e:
  p=D/(Path(e['path']).stem+'.txt');b=p.read_bytes();t.append(dict(path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest(),derived_from=e['path']))
(D/'derivative-bindings.json').write_text(json.dumps(t,indent=2)+'\n');print(out);print(t)
