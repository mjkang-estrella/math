import pathlib,json,hashlib,datetime,urllib.request,urllib.error,sys
D=pathlib.Path(__file__).resolve().parents[1]
DENIED={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org','mathdb.com'}
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in DENIED:raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
def get(key,url):
 p=D/'sources'/key; recp=p.with_name(p.name+'.receipt.json')
 if recp.exists():return
 rec=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  if urllib.parse.urlparse(url).hostname in DENIED:raise RuntimeError('inherited denied host')
  with urllib.request.build_opener(Redirect).open(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=25) as r:data=r.read();rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));p.write_bytes(data)
 except urllib.error.HTTPError as e:
  data=e.read();p.write_bytes(data);rec.update(status=e.code,error=str(e),sha256=hashlib.sha256(data).hexdigest())
  if e.code in (403,429):DENIED.add(urllib.parse.urlparse(url).hostname)
 except Exception as e:rec['error']=str(e)
 recp.write_text(json.dumps(rec,indent=2)+'\n');print(key,rec.get('status',rec.get('error')),flush=True)
if __name__=='__main__':
 for key,url in json.loads(pathlib.Path(sys.argv[1]).read_text()):get(key,url)
