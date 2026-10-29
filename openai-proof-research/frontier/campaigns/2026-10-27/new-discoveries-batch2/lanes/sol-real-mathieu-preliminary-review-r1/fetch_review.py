from pathlib import Path
import urllib.request,json,datetime,hashlib,sys
L=Path(__file__).resolve().parent
jobs=[('oros.pdf','https://files.ele-math.com/articles/jmi-07-49.pdf'),('rss1973.pdf','https://www.e-periodica.ch/cntmng?pid=com-001%3A1973%3A48%3A%3A15')]
p=json.loads((L/'frozen/provenance.json').read_text())
for x in p['http_sourcebytes']:
 if '/commits/' in x['url']:jobs.append(('current-'+Path(x['file']).name,x['url']))
for name,url in jobs:
 rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'file':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-source-review'}),timeout=25) as r: b=r.read();rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(L/name).write_bytes(b)
 except Exception as e:rec['error']=str(e)
 with (L/'http-review.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(json.dumps(rec),flush=True)
