from pathlib import Path
import urllib.request,datetime,hashlib,json
D=Path(__file__).resolve().parent
out=[]
for name in ['1809.07200','2012.02524','1503.05295','1804.03737']:
 url='https://arxiv.org/html/'+name
 row=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),requested_version='latest HTML; document version to be inspected')
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source screening'}),timeout=35) as r:
   b=r.read(12000000); row.update(status=r.status,final_url=r.url)
  p=D/(name+'.html');p.write_bytes(b);row.update(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:row['failure']=str(e)
 out.append(row)
(D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
