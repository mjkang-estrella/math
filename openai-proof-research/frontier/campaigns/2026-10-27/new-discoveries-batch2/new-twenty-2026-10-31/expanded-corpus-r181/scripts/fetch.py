from pathlib import Path
import urllib.request,urllib.error,urllib.parse,json,hashlib,datetime,sys
D=Path(__file__).resolve().parents[1]
blockedfile=D/'outputs/denied-hosts.json'
blocked=set(json.loads(blockedfile.read_text()) if blockedfile.exists() else ['api.crossref.org','www.sciencedirect.com','mathdb.com','export.arxiv.org'])
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in blocked: raise RuntimeError('redirect to denied host stopped: '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
def get(key,url):
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}; host=urllib.parse.urlparse(url).hostname
 try:
  if host in blocked: raise RuntimeError('inherited or current host denial; not requested')
  with urllib.request.build_opener(Redirect).open(urllib.request.Request(url,headers={'User-Agent':'research-r181'}),timeout=25) as r:
   b=r.read(); rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b)); (D/'sources'/key).write_bytes(b)
 except Exception as e:
  rec['error']=str(e)
  if isinstance(e,urllib.error.HTTPError):
   rec['status']=e.code
   if e.code in (403,429): blocked.add(host)
 (D/'sources'/(key+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');blockedfile.write_text(json.dumps(sorted(blocked)))
 print(key,rec.get('status'),rec.get('error',''),rec.get('bytes',''),flush=True)
 return rec
if __name__=='__main__':
 if sys.argv[1]=='heads':
  for key,repo in [('pool','Vilin97/lean-pool'),('omega','the-omega-institute/trureturing'),('openai','openai/math')]:get(key+'-head.json','https://api.github.com/repos/'+repo+'/commits/HEAD')
 elif sys.argv[1]=='papers':
  x=json.loads((D/'extracted.json').read_text())
  for i in sys.argv[2:]:
   a=x[i]['source_url'].rsplit('/',1)[-1];get(a+'.abs.html','https://arxiv.org/abs/'+a); get(a+'.pdf','https://arxiv.org/pdf/'+a)
 else:get(sys.argv[1],sys.argv[2])
