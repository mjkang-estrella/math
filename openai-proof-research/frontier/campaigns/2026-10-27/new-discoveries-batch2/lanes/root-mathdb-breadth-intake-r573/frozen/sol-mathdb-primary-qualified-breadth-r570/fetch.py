from pathlib import Path
import urllib.request,hashlib,json,datetime
D=Path(__file__).resolve().parent
out=[]
for label,version in [('neumann','2512.21103v1'),('bell','2509.05235v1'),('fraction','2601.08461v1'),('outerplanar','2410.00310v1')]:
 url='https://arxiv.org/html/'+version
 row=dict(label=label,url=url,requested_version=version,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(url,timeout=35) as f:b=f.read();row.update(final_url=f.url,status=f.status,content_type=f.headers.get('Content-Type'))
  p=D/(label+'.html');p.write_bytes(b);row.update(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
 except Exception as e:row['failure']=str(e)
 out.append(row);print(row)
(D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
