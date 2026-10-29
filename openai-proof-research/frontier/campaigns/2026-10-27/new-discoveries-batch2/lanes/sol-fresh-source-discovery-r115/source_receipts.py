import urllib.request,hashlib,json,time
from pathlib import Path
lane=Path(__file__).resolve().parent
items=[]
for name,url in [('arxiv-abstract.html','https://arxiv.org/abs/2209.00986'),('successor-ALS.pdf','https://www.iazd.uni-hannover.de/fileadmin/iazd/sambale/pdfs/ALS.pdf')]:
 start=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
 try:
  with urllib.request.urlopen(url,timeout=35) as r:
   data=r.read(2000000);assert len(data)<2000000
   p=lane/'sources'/name;p.write_bytes(data)
   items.append({'url':url,'utc_start':start,'utc_end':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'http_status':r.status,'path':str(p.relative_to(lane)),'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)})
 except Exception as e:items.append({'url':url,'utc_start':start,'error':repr(e)})
(lane/'source-fetch-receipts.json').write_text(json.dumps(items,indent=2)+'\n')
print(json.dumps(items))
