import pathlib,json,hashlib,datetime,urllib.request,urllib.error,urllib.parse,sys
D=pathlib.Path(__file__).resolve().parents[1]
blocked={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org','dblp.uni-trier.de','mathdb.com'}
for p in (D/'sources').glob('*.receipt.json'):
 r=json.loads(p.read_text())
 if r.get('status') in (403,429):blocked.add(urllib.parse.urlparse(r['url']).hostname)
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in blocked:raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
def get(key,url):
 p=D/'sources'/key; recp=p.with_name(p.name+'.receipt.json')
 if recp.exists():return
 rec=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  if urllib.parse.urlparse(url).hostname in blocked:raise RuntimeError('inherited/local denied host; not requested')
  with urllib.request.build_opener(Redirect).open(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=25) as r:
   data=r.read();rec.update(status=r.status,final_url=r.url,headers=dict(r.headers),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));p.write_bytes(data)
 except urllib.error.HTTPError as e:
  data=e.read();p.write_bytes(data);rec.update(status=e.code,error=str(e),sha256=hashlib.sha256(data).hexdigest())
  if e.code in (403,429):blocked.add(urllib.parse.urlparse(url).hostname)
 except Exception as e:rec['error']=str(e)
 recp.write_text(json.dumps(rec,indent=2)+'\n');print(key,rec.get('status',rec.get('error')),flush=True)
if __name__=='__main__':
 if len(sys.argv)>1:get(sys.argv[1],sys.argv[2])
 else:
  for a in dict.fromkeys(x['source_url'].rsplit('/',1)[-1] for x in json.loads((D/'extracted.json').read_text()).values()):get(a+'.html','https://arxiv.org/html/'+a)
