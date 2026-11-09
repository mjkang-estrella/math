from pathlib import Path
import urllib.request,hashlib,json,datetime
D=Path(__file__).resolve().parent
out=[]
for a in ['2511.13693','2510.24280','2601.19775','2601.01211']:
 url='https://arxiv.org/html/'+a+'v1';e={'requested_url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as f:b=f.read();e.update(final_url=f.url,status=f.status)
  p=D/(a+'v1.html');p.write_bytes(b);e.update(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as ex:e['failure']=str(ex)
 out.append(e)
 (D/'source-download-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
