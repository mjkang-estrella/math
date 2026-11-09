from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime,sys
L=Path(__file__).resolve().parents[1]
blocked={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org','mathdb.com','palomar.caltech.edu'}
class Safe(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in blocked:raise RuntimeError('blocked redirect '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
op=urllib.request.build_opener(Safe())
def fetch(url,label):
 if urllib.parse.urlparse(url).hostname in blocked:return
 stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f');base=L/'receipts'/f'{stamp}-{label}'
 r={'url':url,'utc':stamp}
 try:
  with op.open(urllib.request.Request(url,headers={'User-Agent':'research-source-review/1.0'}),timeout=35) as resp:
   data=resp.read();r.update(status=resp.status,final_url=resp.url,headers=dict(resp.headers),sha256=hashlib.sha256(data).hexdigest());base.with_suffix('.body').write_bytes(data)
   if b'captcha' in data[:20000].lower() or b'cf-chl-' in data[:20000].lower():r['challenge']=True;blocked.add(urllib.parse.urlparse(url).hostname)
 except urllib.error.HTTPError as e:
  data=e.read();base.with_suffix('.body').write_bytes(data);r.update(status=e.code,sha256=hashlib.sha256(data).hexdigest())
  if e.code in (403,429):blocked.add(urllib.parse.urlparse(url).hostname)
 except Exception as e:r['error']=str(e)
 base.with_suffix('.json').write_text(json.dumps(r,indent=2));print(label,r.get('status',r.get('error')),flush=True)
 return data if r.get('status')==200 and not r.get('challenge') else None
if __name__=='__main__':
 mode=sys.argv[1]
 if mode=='sources':
  for row in json.loads((L/'reservation.json').read_text())['rows']:
   a=row['source_url'].split('/')[-1]
   if (L/'sources'/f'{a}.pdf').exists():continue
   b=fetch('https://arxiv.org/abs/'+a,a+'-abs')
   if b:(L/'sources'/f'{a}.html').write_bytes(b)
   b=fetch('https://arxiv.org/pdf/'+a,a+'-pdf')
   if b and b.startswith(b'%PDF'):(L/'sources'/f'{a}.pdf').write_bytes(b)
 if mode=='registries':
  for repo in ['Vilin97/lean-pool','openai/math','the-omega-institute/trureturing']:
   b=fetch('https://api.github.com/repos/'+repo+'/commits/HEAD',repo.replace('/','-')+'-head')
   if b:
    sha=json.loads(b)['sha'];(L/'outputs'/ (repo.replace('/','-')+'-head.json')).write_bytes(b)
    b=fetch('https://api.github.com/repos/'+repo+'/git/trees/'+sha+'?recursive=1',repo.replace('/','-')+'-tree')
    if b:(L/'outputs'/(repo.replace('/','-')+'-tree.json')).write_bytes(b)
    if repo=='Vilin97/lean-pool':
     b=fetch('https://raw.githubusercontent.com/'+repo+'/'+sha+'/projects.yml','pool-projects')
     if b:(L/'sources/pool-projects.yml').write_bytes(b)
