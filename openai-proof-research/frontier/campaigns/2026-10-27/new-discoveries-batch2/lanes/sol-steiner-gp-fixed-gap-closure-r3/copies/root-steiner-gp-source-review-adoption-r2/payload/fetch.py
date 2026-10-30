from pathlib import Path
import urllib.request,sys,json,hashlib,datetime
P=Path(__file__).resolve().parent
def fetch(name,url):
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'file':name}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Research source verification (public documents)'})
  with urllib.request.urlopen(req,timeout=22) as f:
   data=f.read(10000001)
   if len(data)>10000000:raise ValueError('response exceeds 10MB bounded retrieval')
   r.update(status=f.status,final_url=f.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
  p=P/'retrieved'/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
 except Exception as e:r['error']=repr(e)
 with (P/'retrieval.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(json.dumps(r));return r
if __name__=='__main__':
 for i in range(1,len(sys.argv),2):fetch(sys.argv[i],sys.argv[i+1])
