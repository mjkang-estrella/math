from pathlib import Path
import os,sys,json,hashlib,datetime,urllib.request,re,subprocess
L=Path(__file__).resolve().parent; B=L.parents[1]; R=B.parents[3]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
def fetch(n,u):
 (L/'sources').mkdir(exist_ok=True);r=dict(utc=now(),url=u,file=n)
 try:
  assert not any(x in u.lower() for x in ['github','codeload','sciencedirect','google.','crossref','export.arxiv','dblp','duckduckgo'])
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical source research'}),timeout=25) as f:
   b=f.read(10000001);assert len(b)<10000001;(L/'sources'/n).write_bytes(b);r.update(status=f.status,final_url=f.url,sha256=sha(b),bytes=len(b))
 except Exception as e:r['error']=str(e)
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(r)

if __name__=="__main__":
 for a in sys.argv[1:]:fetch(*a.split("=",1))
