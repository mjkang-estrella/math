import urllib.request, urllib.error, pathlib, hashlib, json, datetime, sys
url,name=sys.argv[1:]; root=pathlib.Path(__file__).resolve().parent.parent
r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'retry':False}
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-check/1.0'}),timeout=25) as f:
  b=f.read(15000000);r.update(status=f.status,final_url=f.url,headers=dict(f.headers));(root/'sources'/name).write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
(root/'receipts'/(name+'.json')).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
