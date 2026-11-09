import pathlib,json,hashlib,datetime,urllib.request,urllib.parse,urllib.error,sys
D=pathlib.Path(__file__).resolve().parents[1]; S=D/'sources'
blocked={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org'}
class Guard(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in blocked: raise RuntimeError('Denied redirect host '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
opener=urllib.request.build_opener(Guard())
def get(key,url):
 p=S/key;rpath=S/(key+'.receipt.json'); assert not p.exists() and not rpath.exists()
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 if urllib.parse.urlparse(url).hostname in blocked:rec['error']='host denied; not requested'
 else:
  try:
   with opener.open(urllib.request.Request(url,headers={'User-Agent':'Research source verification (bounded requests)'}),timeout=25) as r:
    data=r.read();rec.update(status=r.status,final_url=r.url,headers=dict(r.headers))
   p.write_bytes(data);rec.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),path=str(p))
   if b'checking your browser' in data.lower() or b'captcha' in data[:10000].lower():blocked.add(urllib.parse.urlparse(url).hostname);rec['challenge']=True
  except Exception as e:
   rec['error']=str(e)
   if isinstance(e,urllib.error.HTTPError):
    rec['status']=e.code;data=e.read();p.write_bytes(data);rec.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
    if e.code in (403,429):blocked.add(urllib.parse.urlparse(url).hostname)
 rpath.write_text(json.dumps(rec,indent=2));print(key,rec.get('status',rec.get('error')),flush=True);return rec
if __name__=='__main__':
 if len(sys.argv)>1:get(sys.argv[1],sys.argv[2])
 else:
  for repo,key in [('Vilin97/lean-pool','pool-head'),('openai/math','openai-head'),('the-omega-institute/trureturing','omega-head')]:get(key+'.json','https://api.github.com/repos/'+repo+'/commits/HEAD')
  ids=sorted({o['source_url'].rsplit('/',1)[-1] for o in json.loads((D/'extracted.json').read_text()).values()})
  for a in ids:get(a+'.html','https://arxiv.org/html/'+a)
