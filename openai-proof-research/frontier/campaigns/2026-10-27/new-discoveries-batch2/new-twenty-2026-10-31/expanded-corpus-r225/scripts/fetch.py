import pathlib,json,hashlib,datetime,urllib.request,urllib.error,sys,concurrent.futures
D=pathlib.Path(__file__).resolve().parents[1]
denied={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','sciencedirect.com','dblp.org','mathdb.com'}
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied:raise RuntimeError('redirect to denied host '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
opener=urllib.request.build_opener(Redirect)
def get(key,url):
 p=D/'sources'/key; rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 if p.exists() or pathlib.Path(str(p)+'.receipt.json').exists():return key,'exists'
 if urllib.parse.urlparse(url).hostname in denied:return key,'blocked by inherited denial'
 try:
  with opener.open(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=18) as r:
   data=r.read(18000000);rec.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  p.write_bytes(data);rec.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),path=str(p))
  if b'challenge' in data[:3000].lower() and b'cloudflare' in data[:3000].lower():denied.add(urllib.parse.urlparse(url).hostname);rec['challenge']=True
 except Exception as e:
  rec['error']=str(e)
  if isinstance(e,urllib.error.HTTPError):
   rec['status']=e.code
   if e.code in (403,429):denied.add(urllib.parse.urlparse(url).hostname)
 pathlib.Path(str(p)+'.receipt.json').write_text(json.dumps(rec,indent=2)+'\n');return key,rec.get('status',rec.get('error')),rec.get('bytes')
if __name__=='__main__':
 if len(sys.argv)>1: print(get(sys.argv[1],sys.argv[2]),flush=True)
 else:
  x=json.loads((D/'extracted.json').read_text());seen=set()
  for o in x.values():
   a=o['source_url'].rsplit('/',1)[-1]
   if a in seen:continue
   seen.add(a)
   print(get(a+'-abs.html','https://arxiv.org/abs/'+a),flush=True)
   print(get(a+'.html','https://arxiv.org/html/'+a),flush=True)
  (D/'sources/denied-hosts.json').write_text(json.dumps(sorted(denied),indent=2)+'\n')
