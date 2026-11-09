from pathlib import Path
import urllib.request,urllib.parse,json,hashlib,datetime,sys
L=Path(__file__).resolve().parent
P=L/'primary';P.mkdir(exist_ok=True)
def get(url,name):
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Academic research bounded retrieval'})
  with urllib.request.urlopen(req,timeout=25) as r:
   data=r.read(7000000);rec.update(status=r.status,final_url=r.url,size=len(data))
  p=P/name;p.write_bytes(data);rec.update(path=str(p),sha256=hashlib.sha256(data).hexdigest())
  print(name,data[:180] if '.pdf' in name else data.decode(errors='replace')[:18000])
 except Exception as e: rec['failure']=str(e);print(name,str(e))
 with (L/'retrieval.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 return rec
if __name__=='__main__':
 for i,q in enumerate(sys.argv[1:]):
  get('https://www.bing.com/search?format=rss&q='+urllib.parse.quote(q),'search-'+str(i)+'-'+hashlib.sha256(q.encode()).hexdigest()[:8]+'.xml')
