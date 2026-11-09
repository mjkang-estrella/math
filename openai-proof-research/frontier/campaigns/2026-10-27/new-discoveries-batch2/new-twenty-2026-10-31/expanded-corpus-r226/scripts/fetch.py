from pathlib import Path
import urllib.request,urllib.error,urllib.parse,json,hashlib,datetime,sys
L=Path(__file__).resolve().parents[1]
denied={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','sciencedirect.com','dblp.org'}
class R(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlsplit(newurl).hostname in denied: raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
for url in sys.argv[1:]:
 host=urllib.parse.urlsplit(url).hostname
 if host in denied: continue
 stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'); key=stamp+'-'+hashlib.sha256(url.encode()).hexdigest()[:12]
 receipt={'url':url,'utc':stamp}
 try:
  resp=urllib.request.build_opener(R()).open(urllib.request.Request(url,headers={'User-Agent':'MathResearch/1.0'}),timeout=25)
  data=resp.read(18000000); receipt.update(status=resp.status,final_url=resp.url,headers=dict(resp.headers))
 except urllib.error.HTTPError as e:
  data=e.read(); receipt.update(status=e.code,error=str(e));
  if e.code in (403,429): denied.add(host)
 except Exception as e: data=b''; receipt['error']=repr(e)
 receipt.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),body=key+'.body')
 (L/'receipts'/ (key+'.body')).write_bytes(data)
 (L/'receipts'/ (key+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
 print(url,receipt.get('status'),receipt.get('error',''),key,len(data),flush=True)
