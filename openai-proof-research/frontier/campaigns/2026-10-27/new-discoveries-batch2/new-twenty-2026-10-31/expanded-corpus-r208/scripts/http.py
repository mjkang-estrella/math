import urllib.request,urllib.error,urllib.parse,pathlib,json,hashlib,datetime,sys
D=pathlib.Path(__file__).resolve().parents[1]
state=D/'outputs/denied-hosts.json'
denied=set(json.loads(state.read_text())) if state.exists() else {'api.crossref.org','api.semanticscholar.org','export.arxiv.org','api.arxiv.org','www.sciencedirect.com','mathdb.com','palomar'}
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,h,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied:raise RuntimeError('redirect to denied host '+newurl)
  return super().redirect_request(req,fp,code,msg,h,newurl)
def get(key,url):
 p=D/'sources'/key; rec=p.with_name(p.name+'.receipt.json')
 if rec.exists():raise RuntimeError('receipt exists '+key)
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
 host=urllib.parse.urlparse(url).hostname
 try:
  if host in denied:raise RuntimeError('denied host skipped')
  with urllib.request.build_opener(Redirect()).open(urllib.request.Request(url,headers={'User-Agent':'Research source-check/1.0'}),timeout=25) as h:
   b=h.read();r.update(status=h.status,final_url=h.url,headers=dict(h.headers))
  p.write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),path=str(p))
  if b'challenge-platform' in b or b'captcha' in b.lower()[:10000]:denied.add(host);r['challenge_detected']=True
 except urllib.error.HTTPError as e:
  b=e.read();p.write_bytes(b);r.update(status=e.code,error=str(e),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if e.code in (403,429):denied.add(host)
 except Exception as e:r['error']=str(e)
 rec.write_text(json.dumps(r,indent=2)+'\n');state.write_text(json.dumps(sorted(denied)))
 print(key,r.get('status',r.get('error')),r.get('bytes'),flush=True);return r
if __name__=='__main__':
 for key,url in json.loads(pathlib.Path(sys.argv[1]).read_text()):get(key,url)
