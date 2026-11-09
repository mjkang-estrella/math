from pathlib import Path
import urllib.request,datetime,hashlib,json
O=Path(__file__).resolve().parent;P=O/'primary';P.mkdir(exist_ok=True)
urls=[('sectors-definitions','https://www.numdam.org/item/10.1007/s10240-019-00112-x.pdf'),('sectorial-descent','https://web.math.princeton.edu/~jpardon/manuscripts/14_descent.pdf'),('simplex-survey','https://www.math.ualberta.ca/~alexandr/OrganizedPapers/AL-simp-wv.pdf')]
for name,url in urls:
 meta=dict(url=url,requested_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),version='exact response bytes; publication correspondence not yet inspected')
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-review/1.0'}),timeout=25) as r:
   data=r.read(12*1024*1024+1);assert len(data)<=12*1024*1024
   meta.update(status=r.status,final_url=r.url,headers=dict(r.headers),size=len(data),sha256=hashlib.sha256(data).hexdigest(),retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
   (P/(name+'.pdf')).write_bytes(data)
 except Exception as e:meta.update(error=repr(e))
 (P/(name+'.meta.json')).write_text(json.dumps(meta,indent=2)+'\n')
 print(name,json.dumps({k:v for k,v in meta.items() if k!='headers'}))
