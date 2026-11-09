import urllib.request,urllib.error,pathlib,json,hashlib,datetime,sys,urllib.parse
D=pathlib.Path(__file__).resolve().parents[1]
blocked={'api.crossref.org','www.sciencedirect.com','mathdb.com','export.arxiv.org'}
class Guard(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in blocked:raise RuntimeError('Blocked redirect '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
op=urllib.request.build_opener(Guard())
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 p=D/'sources'/name
 if p.with_suffix('.receipt.json').exists():raise RuntimeError('Receipt exists '+name)
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 if urllib.parse.urlparse(url).hostname in blocked:rec['error']='Inherited denied host; not requested'
 else:
  try:
   with op.open(urllib.request.Request(url,headers={'User-Agent':'Mathematical-research/1.0'}),timeout=25) as r:
    b=r.read();rec.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  except urllib.error.HTTPError as e:
   b=e.read();rec.update(status=e.code,error=str(e),headers=dict(e.headers));
   if e.code in (403,429):blocked.add(urllib.parse.urlparse(url).hostname)
  except Exception as e:b=b'';rec['error']=str(e)
  if b:p.with_suffix('.body').write_bytes(b);rec.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 p.with_suffix('.receipt.json').write_text(json.dumps(rec,indent=2));print(name,rec.get('status'),rec.get('error',''),rec.get('bytes'))
