import urllib.request,urllib.error,hashlib,json,datetime
from pathlib import Path
P=Path(__file__).parent
blocked=set(); receipts=[]
def fetch(name,url):
 host=urllib.parse.urlparse(url).netloc
 if host in blocked: raise RuntimeError("host blocked after access limit")
 r={"url":url,"file":"sources/"+name,"retrieved_utc":datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as f:
   r["status"]=f.status; data=f.read(12000000)
  if any(s in data[:10000].lower() for s in [b"verify you are human",b"just a moment..."]):
   blocked.add(host); r["error"]="challenge"
  else:
   (P/"sources"/name).write_bytes(data);r.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
 except urllib.error.HTTPError as e:
  r.update(status=e.code,error=str(e))
  if e.code in [403,429]:blocked.add(host)
 except Exception as e:r["error"]=str(e)
 receipts.append(r);(P/"retrievals.json").write_text(json.dumps(receipts,indent=2));print(r)
if __name__=="__main__":
 fetch("quadratic-original.html","https://arxiv.org/html/1606.05039v1")
 fetch("quadratic-resolution.pdf","https://ac.inf.elte.hu/Vol_046_2017/doi/123_46.pdf")
 fetch("discrete-log.html","https://arxiv.org/html/math/0401013v2")
