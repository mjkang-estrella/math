from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,sys
r=Path(__file__).resolve().parents[1]
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 rec=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-review/1.0'}),timeout=35) as x:b=x.read();rec.update(status=x.status,final_url=x.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(r/'sources'/name).write_bytes(b)
 except Exception as e:rec.update(error=str(e),status=getattr(e,'code',None))
 (r/'receipts'/(name+'.json')).write_text(json.dumps(rec,indent=2));print(name,rec)
