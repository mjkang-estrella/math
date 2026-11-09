import urllib.request,urllib.error,pathlib,json,hashlib,datetime,sys
D=pathlib.Path(__file__).resolve().parents[1];url=sys.argv[2];tag=sys.argv[1]
r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Math independent research review (public documents)'}),timeout=35) as f:
  b=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(D/'receipts'/tag).write_bytes(b)
except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
(D/'receipts'/(tag+'.receipt.json')).write_text(json.dumps(r,indent=2));print(json.dumps(r))
