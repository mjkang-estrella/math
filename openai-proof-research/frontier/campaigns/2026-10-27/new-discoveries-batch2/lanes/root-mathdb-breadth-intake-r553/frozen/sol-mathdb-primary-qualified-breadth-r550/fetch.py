import urllib.request,hashlib,json,datetime
from pathlib import Path
D=Path(__file__).parent;out=[]
for a in ['1054','4330','17469','3389']:
 u='https://ems.press/journals/owr/articles/'+a
 try:
  with urllib.request.urlopen(u,timeout=25) as r:b=r.read();status=r.status
  p=D/(a+'.html');p.write_bytes(b)
  out.append(dict(url=u,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest(),status=status))
 except Exception as e:out.append(dict(url=u,error=str(e),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
(D/'retrieval-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
