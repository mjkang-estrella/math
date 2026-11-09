import pathlib,urllib.request,urllib.error,json,hashlib,datetime,sys,time
D=pathlib.Path(__file__).resolve().parents[1]
class Safe(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlsplit(newurl).hostname in denied: raise RuntimeError('denied redirect host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
denied=set(['www.sciencedirect.com','sciencedirect.com','mathdb.com','palomar.com'])
op=urllib.request.build_opener(Safe())
for url in sys.argv[1:]:
 tag=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f'); p=D/'sources'/tag;p.mkdir()
 r={'url':url,'utc':tag}
 try:
  if urllib.parse.urlsplit(url).hostname in denied:raise RuntimeError('previously denied host')
  with op.open(urllib.request.Request(url,headers={'User-Agent':'MathematicsResearch/1.0'}),timeout=18) as f:
   b=f.read();r.update(status=f.status,final_url=f.url,headers=dict(f.headers));(p/'body').write_bytes(b);r['sha256']=hashlib.sha256(b).hexdigest();r['bytes']=len(b)
 except urllib.error.HTTPError as e:
  b=e.read();(p/'body').write_bytes(b);r.update(status=e.code,error=str(e),sha256=hashlib.sha256(b).hexdigest());
  if e.code in (403,429):denied.add(urllib.parse.urlsplit(url).hostname)
 except Exception as e:r['error']=str(e)
 (p/'receipt.json').write_text(json.dumps(r,indent=2));print(str(p.relative_to(D)),url,r.get('status'),r.get('error',''),flush=True)
 time.sleep(1)
