from pathlib import Path
import urllib.request,json,hashlib,datetime
D=Path(__file__).parent; rows=[]
for n in ['1452','1111','1464']:
 u='https://ems.press/journals/owr/articles/'+n;t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(u,timeout=25) as f:b=f.read();url=f.url;ct=f.headers.get('Content-Type')
  p=D/('owr'+n+'.html');p.write_bytes(b);rows.append(dict(url=u,final_url=url,utc=t,path=str(p.resolve()),size=len(b),sha256=hashlib.sha256(b).hexdigest(),content_type=ct));print(n,len(b))
 except Exception as e:rows.append(dict(url=u,utc=t,failure=str(e)));print(n,str(e))
(D/'source-provenance.json').write_text(json.dumps(rows,indent=2)+'\n')
