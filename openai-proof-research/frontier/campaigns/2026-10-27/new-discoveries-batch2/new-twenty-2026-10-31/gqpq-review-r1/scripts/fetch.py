import urllib.request,urllib.error,hashlib,datetime,json,sys,pathlib
D=pathlib.Path(__file__).resolve().parents[1]/'receipts'
name,url=sys.argv[1:];r=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Independent mathematical review (public research)'}),timeout=35) as f:
  b=f.read(20000000);r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(D/name).write_bytes(b)
except urllib.error.HTTPError as e:r.update(status=e.code,error=str(e))
except Exception as e:r.update(status='network_error',error=str(e))
(D/(name+'.json')).write_text(json.dumps(r,indent=2));print(json.dumps(r))
