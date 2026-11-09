import urllib.request,urllib.error,urllib.parse,json,pathlib,hashlib,datetime,sys
D=pathlib.Path(__file__).resolve().parents[1]
DENIED={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','api.arxiv.org','www.sciencedirect.com','sciencedirect.com','dblp.org'}
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in DENIED: raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
def get(key,url):
 p=D/'receipts'/key;p.mkdir(exist_ok=False)
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 if urllib.parse.urlparse(url).hostname in DENIED:rec['error']='host previously denied; no request'
 else:
  try:
   with urllib.request.build_opener(Redirect()).open(urllib.request.Request(url,headers={'User-Agent':'Mathematical research verification'}),timeout=25) as r:
    b=r.read(20000000);rec.update(status=r.status,final_url=r.url,headers=dict(r.headers),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(p/'body').write_bytes(b)
    if b'captcha' in b.lower() or b'challenge-platform' in b.lower():DENIED.add(urllib.parse.urlparse(r.url).hostname);rec['challenge_marker']=True
  except urllib.error.HTTPError as e:
   b=e.read();(p/'body').write_bytes(b);rec.update(status=e.code,sha256=hashlib.sha256(b).hexdigest(),error=str(e))
   if e.code in (403,429):DENIED.add(urllib.parse.urlparse(url).hostname)
  except Exception as e:rec['error']=str(e)
 (p/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(key,rec.get('status'),rec.get('error',''),flush=True)
 return rec
if __name__=='__main__':
 x=json.loads((D/'extracted.json').read_text())
 for i,o in x.items():
  a=o['source_url'].rsplit('/',1)[-1];get(i+'-abs',o['source_url']);get(i+'-html','https://arxiv.org/html/'+a)
 get('leanpool-head','https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD')
 if (D/'receipts/leanpool-head/body').exists():
  o=json.loads((D/'receipts/leanpool-head/body').read_text());s=o.get('sha')
  if s:
   get('leanpool-projects','https://raw.githubusercontent.com/Vilin97/lean-pool/'+s+'/projects.yml');get('leanpool-tree','https://api.github.com/repos/Vilin97/lean-pool/git/trees/'+s+'?recursive=1')
 get('github-lean-search','https://api.github.com/search/repositories?q='+urllib.parse.quote('lean "dominion"'))
 (D/'outputs/denied-hosts.json').write_text(json.dumps(sorted(DENIED),indent=2)+'\n')
