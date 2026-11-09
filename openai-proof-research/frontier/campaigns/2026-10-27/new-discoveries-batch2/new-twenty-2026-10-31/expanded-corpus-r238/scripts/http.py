import urllib.request,urllib.error,urllib.parse,pathlib,json,hashlib,datetime,sys
D=pathlib.Path(__file__).resolve().parents[1]; S=D/'sources'
denied={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','api.arxiv.org','www.sciencedirect.com','sciencedirect.com','dblp.org'}
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied:raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
def get(key,url):
 p=S/key; recpath=S/(key+'.receipt.json')
 if recpath.exists():return json.loads(recpath.read_text())
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 if urllib.parse.urlparse(url).hostname in denied:rec['error']='inherited/session host denial; not requested'
 else:
  try:
   with urllib.request.build_opener(Redirect()).open(urllib.request.Request(url,headers={'User-Agent':'Research verification'}),timeout=20) as r:
    b=r.read();rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));p.write_bytes(b)
  except Exception as e:
   rec['error']=str(e)
   if isinstance(e,urllib.error.HTTPError):
    b=e.read();p.write_bytes(b);rec.update(status=e.code,sha256=hashlib.sha256(b).hexdigest())
    if e.code in (403,429):denied.add(urllib.parse.urlparse(url).hostname)
 recpath.write_text(json.dumps(rec,indent=2)+'\n');print(key,rec.get('status',rec.get('error')),flush=True);return rec
if __name__=='__main__':
 for o in json.loads((D/'extracted.json').read_text()).values():
  a=o['source_url'].rsplit('/',1)[-1];get(a+'.abs.html',o['source_url']);get(a+'.pdf','https://arxiv.org/pdf/'+a)
 for repo in ['openai/math','Vilin97/lean-pool','the-omega-institute/trureturing']:
  k=repo.replace('/','-');get(k+'-head.json','https://api.github.com/repos/'+repo+'/commits/HEAD')
  p=S/(k+'-head.json')
  if p.exists():
   try:sha=json.loads(p.read_text())['sha'];get(k+'-tree.json','https://api.github.com/repos/'+repo+'/git/trees/'+sha+'?recursive=1')
   except (KeyError,ValueError):pass
