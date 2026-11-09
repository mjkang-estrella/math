from pathlib import Path
import urllib.request, urllib.error, hashlib,json,datetime,sys
L=Path(__file__).resolve().parents[1]
def fetch(url,name):
 t=datetime.datetime.now(datetime.timezone.utc).isoformat(); rec={'utc':t,'url':url,'name':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-inspection/1.0'}),timeout=35) as r:
   b=r.read(16000000);rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(L/'sources'/name).write_bytes(b)
 except Exception as e:rec.update(error=str(e))
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(rec)
if __name__=='__main__':fetch(sys.argv[1],sys.argv[2])
