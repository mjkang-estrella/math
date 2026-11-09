import sys,pathlib,urllib.request,urllib.error,hashlib,json,datetime
D=pathlib.Path(sys.argv[1]); urls=sys.argv[2:]; denied=set(); receipts=[]
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied:raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
op=urllib.request.build_opener(Redirect())
for url in urls:
 host=urllib.parse.urlparse(url).hostname
 if host in denied:continue
 folder=D/'downloads'/('request-'+datetime.datetime.now().strftime('%H%M%S%f'));folder.mkdir()
 r=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with op.open(urllib.request.Request(url,headers={'User-Agent':'Math research source check'}),timeout=25) as f:
   data=f.read(15000000);r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(folder/'body').write_bytes(data)
 except urllib.error.HTTPError as e:
  r.update(status=e.code,error=str(e));denied.add(host) if e.code in (403,429) else None
 except Exception as e:r['error']=str(e)
 (folder/'receipt.json').write_text(json.dumps(r,indent=2));print(r,flush=True)
