from pathlib import Path
import urllib.request, urllib.error, json, hashlib, datetime, sys
D=Path(__file__).resolve().parents[1]; denied={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','api.arxiv.org','www.sciencedirect.com','dblp.org'}
from urllib.parse import urlparse
class Guard(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urlparse(newurl).hostname in denied: raise RuntimeError('Redirect to denied host '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
op=urllib.request.build_opener(Guard())
def get(key,url):
 p=D/'sources'/key; rpath=D/'sources'/(key+'.receipt.json')
 if p.exists() or rpath.exists(): print('preserved',key,flush=True); return
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  if urlparse(url).hostname in denied: raise RuntimeError('denied host')
  with op.open(urllib.request.Request(url,headers={'User-Agent':'Research source checking'}),timeout=15) as r:
   data=r.read();rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));p.write_bytes(data)
 except urllib.error.HTTPError as e:
  data=e.read();p.write_bytes(data);rec.update(status=e.code,error=str(e),sha256=hashlib.sha256(data).hexdigest());
  if e.code in (403,429):denied.add(urlparse(url).hostname)
 except Exception as e:rec['error']=str(e)
 rpath.write_text(json.dumps(rec,indent=2)+'\n'); print(key,rec.get('status',rec.get('error')),flush=True)
if __name__=='__main__':
 if len(sys.argv)>1:
  for i in range(1,len(sys.argv),2):get(sys.argv[i],sys.argv[i+1])
 else:
  x=json.loads((D/'extracted.json').read_text()); ids=list(dict.fromkeys(o['source_url'].rsplit('/',1)[-1] for o in x.values()))
  for a in ids:get(a+'.abs.html','https://arxiv.org/abs/'+a)
