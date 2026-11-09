import pathlib,json,hashlib,datetime,urllib.request,urllib.error,sys
D=pathlib.Path(__file__).resolve().parents[1]
DENIED={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org','mathdb.com'}
p=D/'sources/denied.json'
if p.exists(): DENIED.update(json.loads(p.read_text()))
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in DENIED:raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
def get(key,url):
 dest=D/'sources'/key; recpath=dest.with_name(dest.name+'.receipt.json')
 if recpath.exists():return 'existing '+key
 host=urllib.parse.urlparse(url).hostname
 if host in DENIED:return 'skipped denied '+host
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.build_opener(Redirect()).open(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=25) as r:
   data=r.read();rec.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  dest.open('xb').write(data);rec.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  if b'Just a moment' in data[:30000] or b'Checking your browser' in data[:30000]:DENIED.add(host);rec['challenge']=True
 except Exception as e:
  rec['error']=str(e)
  if isinstance(e,urllib.error.HTTPError):
   rec['status']=e.code
   if e.code in (403,429):DENIED.add(host)
 recpath.open('x').write(json.dumps(rec,indent=2)+'\n');p.write_text(json.dumps(sorted(DENIED)))
 return key,rec.get('status'),rec.get('error'),rec.get('bytes')
if __name__=='__main__':
 if len(sys.argv)>2:print(get(sys.argv[1],sys.argv[2]),flush=True)
 else:
  for o in json.loads((D/'extracted.json').read_text()).values():
   a=o['source_url'].rsplit('/',1)[-1];print(get(a+'.abs.html',o['source_url']),flush=True)
