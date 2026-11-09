import pathlib,urllib.request,urllib.error,urllib.parse,json,hashlib,datetime,sys
L=pathlib.Path(__file__).resolve().parents[1]; D=L/'receipts'; D.mkdir(exist_ok=True)
denied={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org'}
for p in D.glob('*.json'):
 try:
  r=json.loads(p.read_text())
  if r.get('status') in [403,429] or r.get('challenge'):denied.add(urllib.parse.urlparse(r['url']).hostname)
 except:pass
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied:raise RuntimeError('denied redirect host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
for url in sys.argv[1:]:
 stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f'); prefix=D/stamp
 r={'utc':stamp,'url':url}
 if urllib.parse.urlparse(url).hostname in denied:r['status']='blocked_by_inherited_denial'
 else:
  try:
   resp=urllib.request.build_opener(Redirect).open(urllib.request.Request(url,headers={'User-Agent':'Research-source-check/1.0'}),timeout=35)
   data=resp.read();r.update(status=resp.status,final_url=resp.url,headers=dict(resp.headers))
  except urllib.error.HTTPError as e:data=e.read();r.update(status=e.code,headers=dict(e.headers))
  except Exception as e:data=b'';r.update(status='error',error=str(e))
  r['sha256']=hashlib.sha256(data).hexdigest();r['body_file']=prefix.name+'.body';prefix.with_suffix('.body').write_bytes(data)
  if r.get('status') in [403,429]:denied.add(urllib.parse.urlparse(url).hostname)
 prefix.with_suffix('.json').write_text(json.dumps(r,indent=2));print(json.dumps(r))
