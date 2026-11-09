import pathlib,urllib.request,urllib.error,urllib.parse,json,hashlib,datetime,sys,time
L=pathlib.Path(__file__).resolve().parents[1]
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied: raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
denied={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org'}
for p in (L/'receipts').glob('http-*.json'):
 r=json.loads(p.read_text())
 if r.get('status') in [403,429] or r.get('challenge'): denied.add(urllib.parse.urlparse(r['url']).hostname)
def fetch(url):
 host=urllib.parse.urlparse(url).hostname
 n=1
 while True:
  try:
   with (L/f'receipts/http-{n:04d}.json').open('x') as z:z.write(json.dumps({'url':url,'status':'pending'}))
   break
  except FileExistsError:n+=1
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}; data=b''
 if host in denied:r['status']='skipped_denied'
 else:
  try:
   with urllib.request.build_opener(Redirect()).open(urllib.request.Request(url,headers={'User-Agent':'Research source verification (read-only)'}),timeout=25) as f:
    data=f.read();r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
  except urllib.error.HTTPError as e:r.update(status=e.code,error=str(e));data=e.read()
  except Exception as e:r.update(status='error',error=str(e))
  r['challenge']=any(x in data[:100000].lower() for x in [b'verify you are human',b'just a moment...',b'bot challenge'])
  if r.get('status') in [403,429] or r.get('challenge'):denied.add(host)
 r.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),body=f'sources/http-{n:04d}.bin')
 (L/r['body']).write_bytes(data);(L/f'receipts/http-{n:04d}.json').write_text(json.dumps(r,indent=2));print(n,r['status'],url,len(data),flush=True)
 return r,data
if __name__=='__main__':
 for url in sys.argv[1:]:fetch(url)
