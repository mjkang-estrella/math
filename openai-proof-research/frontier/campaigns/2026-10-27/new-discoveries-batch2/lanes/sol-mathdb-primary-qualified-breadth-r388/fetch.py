from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime
R=Path(__file__).resolve().parent;(R/'evidence').mkdir(exist_ok=True); out=[];blocked=set()
urls=[('404655-primary.html','https://ems.press/journals/owr/articles/14298158'),('336882-primary.pdf','https://arxiv.org/pdf/1708.06076'),('352845-primary.pdf','https://arxiv.org/pdf/2112.03361'),('381643-primary.pdf','https://arxiv.org/pdf/2112.08503'),('373857-primary.pdf','https://arxiv.org/pdf/2603.25113')]
for name,url in urls:
 host=urllib.parse.urlparse(url).netloc
 if host in blocked:out.append({'url':url,'status':'not_attempted_host_hold'});continue
 e={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source qualification'}),timeout=25) as f:
   b=f.read(12000000);e.update(final_url=f.url,http_status=f.status,headers=dict(f.headers))
  p=R/'evidence'/name;p.write_bytes(b);e.update(path=str(p.relative_to(R)),size=len(b),sha256=hashlib.sha256(b).hexdigest(),status='retained_before_extraction')
 except Exception as ex:
  e.update(status='failed',error=str(ex))
  if getattr(ex,'code',None) in [403,429]:blocked.add(host)
 out.append(e);(R/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(name,e['status'])
