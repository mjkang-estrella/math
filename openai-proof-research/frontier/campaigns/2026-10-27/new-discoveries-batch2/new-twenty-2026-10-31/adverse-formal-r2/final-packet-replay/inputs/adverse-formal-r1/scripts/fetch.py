from pathlib import Path
import urllib.request, urllib.error, hashlib,json,datetime,sys
root=Path(__file__).resolve().parents[1]
name,url=sys.argv[1:]
receipt=root/'receipts'/f'{name}.json'
if receipt.exists():raise SystemExit('Refuse repeat route: receipt exists')
rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'retries':0}
try:
 r=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check/1.0'}),timeout=25)
 b=r.read(); dest=root/'sources'/name;dest.write_bytes(b)
 rec.update(status=r.status,final_url=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),path=str(dest.relative_to(root)))
except Exception as e:rec.update(error=str(e),status=getattr(e,'code',None))
receipt.write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec))
