import pathlib,urllib.request,urllib.error,urllib.parse,json,hashlib,datetime,sys
L=pathlib.Path(__file__).resolve().parents[1]; D=L/'http'; D.mkdir(exist_ok=True)
denied={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','api.arxiv.org','www.sciencedirect.com','sciencedirect.com','dblp.org'}
for p in D.glob('*/receipt.json'):
 r=json.loads(p.read_text())
 if r.get('status') in (403,429) or r.get('challenge'): denied.add(urllib.parse.urlsplit(r['url']).hostname)
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,hdrs,url):
  if urllib.parse.urlsplit(url).hostname in denied: raise RuntimeError('redirect to denied host '+url)
  return super().redirect_request(req,fp,code,msg,hdrs,url)
op=urllib.request.build_opener(Redirect)
for name,url in json.loads(pathlib.Path(sys.argv[1]).read_text()):
 dest=D/name
 if dest.exists(): print(name,'EXISTS, skipped'); continue
 dest.mkdir(); r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 if urllib.parse.urlsplit(url).hostname in denied: r['error']='host denied; no request'
 else:
  try:
   resp=op.open(urllib.request.Request(url,headers={'User-Agent':'MathResearch/1.0'}),timeout=18)
   data=resp.read(); r.update(status=resp.status,final_url=resp.url,headers=dict(resp.headers)); (dest/'body').write_bytes(data);r['sha256']=hashlib.sha256(data).hexdigest()
   r['challenge']=b'Just a moment' in data[:20000] or b'captcha' in data[:20000].lower()
  except urllib.error.HTTPError as e:
   data=e.read();(dest/'body').write_bytes(data);r.update(status=e.code,headers=dict(e.headers),sha256=hashlib.sha256(data).hexdigest())
  except Exception as e:r['error']=str(e)
  if r.get('status') in (403,429) or r.get('challenge'):denied.add(urllib.parse.urlsplit(url).hostname)
 (dest/'receipt.json').write_text(json.dumps(r,indent=2)); print(name,r.get('status',r.get('error')),flush=True)
