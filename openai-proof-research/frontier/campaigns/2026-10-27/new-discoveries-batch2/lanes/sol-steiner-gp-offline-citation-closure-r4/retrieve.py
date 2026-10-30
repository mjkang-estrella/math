from setup import *
import urllib.request,urllib.parse,urllib.error,sys
DENY=('github.com','api.github.com','raw.githubusercontent.com','codeload.github.com','sciencedirect.com')
def allowed(u):
 host=urllib.parse.urlparse(u).hostname or ''
 assert not any(host==x or host.endswith('.'+x) for x in DENY),u
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  allowed(newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
def fetch(label,url):
 allowed(url);p=HERE/'retrieved'/label;p.parent.mkdir(exist_ok=True)
 receipt={'utc_start':utc(),'url':url,'file':str(p.relative_to(HERE))}
 try:
  with urllib.request.build_opener(Redirect()).open(urllib.request.Request(url,headers={'User-Agent':'Research-review/1.0'}),timeout=25) as r:
   receipt.update(status=r.status,final_url=r.url,content_type=r.headers.get('Content-Type'))
   b=r.read(10000001);assert len(b)<=10000000,'10MB application bound';p.write_bytes(b)
   receipt.update(bytes=len(b),sha256=sha(p))
 except Exception as e:receipt['error']=str(e)
 receipt['utc_end']=utc()
 with (HERE/'access-receipts.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
 print(json.dumps(receipt))
if __name__=='__main__':fetch(sys.argv[1],sys.argv[2])
