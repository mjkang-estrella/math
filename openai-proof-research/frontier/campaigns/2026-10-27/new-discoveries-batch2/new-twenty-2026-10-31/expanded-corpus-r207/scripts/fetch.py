import urllib.request,urllib.error,urllib.parse,json,hashlib,datetime,sys,time
from pathlib import Path
L=Path(__file__).resolve().parents[1]
def fetch(url,label):
 folder=L/'sources'/(label+'-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f')); folder.mkdir(); denied=set(json.loads((L/'outputs/denied-hosts.json').read_text())) if (L/'outputs/denied-hosts.json').exists() else set()
 class Guard(urllib.request.HTTPRedirectHandler):
  def redirect_request(self,req,fp,code,msg,headers,newurl):
   if urllib.parse.urlparse(newurl).hostname in denied: raise RuntimeError('redirect to denied host blocked')
   return super().redirect_request(req,fp,code,msg,headers,newurl)
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  if urllib.parse.urlparse(url).hostname in denied: raise RuntimeError('host already denied; not requested')
  response=urllib.request.build_opener(Guard).open(urllib.request.Request(url,headers={'User-Agent':'MathematicsResearch/1.0'}),timeout=25)
  body=response.read(); rec.update(status=response.status,final_url=response.url,headers=dict(response.headers))
 except urllib.error.HTTPError as e:
  body=e.read(); rec.update(status=e.code,headers=dict(e.headers));
  if e.code in (403,429): denied.add(urllib.parse.urlparse(e.url).hostname)
 except Exception as e: body=b''; rec['error']=str(e)
 rec['sha256']=hashlib.sha256(body).hexdigest(); (folder/'body').write_bytes(body); (folder/'receipt.json').write_text(json.dumps(rec,indent=2)); (L/'outputs/denied-hosts.json').write_text(json.dumps(sorted(denied))); print(label, rec.get('status',rec.get('error')),folder.name,flush=True); return body,rec,str(folder)
if __name__=='__main__': fetch(sys.argv[1],sys.argv[2])
