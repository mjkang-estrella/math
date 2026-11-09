import pathlib,json,hashlib,datetime,urllib.request,urllib.error,sys
D=pathlib.Path(__file__).resolve().parents[1]
DENIED={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org','mathdb.com'}
db=D/'sources/denied.json'
if db.exists(): DENIED.update(json.loads(db.read_text()))
class Safe(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  from urllib.parse import urlparse
  if urlparse(newurl).hostname in DENIED: raise RuntimeError('redirect denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
def get(key,url):
 from urllib.parse import urlparse
 host=urlparse(url).hostname
 p=D/'sources'/key; receipt=p.with_name(p.name+'.receipt.json')
 if receipt.exists(): print(key,'existing receipt');return
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  if host in DENIED: raise RuntimeError('inherited or session denied host')
  with urllib.request.build_opener(Safe()).open(urllib.request.Request(url,headers={'User-Agent':'Math research; source verification'}),timeout=18) as r:
   data=r.read();rec.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  if b'captcha' in data[:10000].lower() or b'just a moment' in data[:10000].lower():
   DENIED.add(host);rec['challenge']=True
  p.write_bytes(data);rec.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),path=str(p))
 except Exception as e:
  rec['error']=str(e)
  if isinstance(e,urllib.error.HTTPError):
   rec['status']=e.code
   if e.code in (403,429): DENIED.add(host)
 receipt.write_text(json.dumps(rec,indent=2)+'\n');db.write_text(json.dumps(sorted(DENIED))+'\n');print(key,rec.get('status'),rec.get('error'),flush=True)
if __name__=='__main__':
 for key,url in json.loads(pathlib.Path(sys.argv[1]).read_text()):get(key,url)
