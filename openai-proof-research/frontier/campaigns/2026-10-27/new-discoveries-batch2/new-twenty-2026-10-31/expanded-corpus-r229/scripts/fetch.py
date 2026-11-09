import urllib.request, urllib.error, urllib.parse, pathlib, json, hashlib, datetime, sys
D=pathlib.Path(__file__).resolve().parents[1]
DENIED={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org','mathdb.com'}
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in DENIED: raise RuntimeError('denied redirect host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
def get(key,url):
 p=D/'sources'/key; receipt=D/'receipts'/(key+'.json')
 if receipt.exists(): return
 now=datetime.datetime.now(datetime.timezone.utc).isoformat(); r={'url':url,'utc':now}
 if urllib.parse.urlparse(url).hostname in DENIED:r['error']='inherited denial; no request'
 else:
  try:
   with urllib.request.build_opener(Redirect()).open(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=18) as f:
    data=f.read();r.update(status=f.status,final_url=f.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
   p.write_bytes(data)
   if b'Just a moment' in data or b'captcha' in data[:3000].lower():DENIED.add(urllib.parse.urlparse(url).hostname);r['challenge']=True
  except Exception as e:
   r['error']=str(e)
   if isinstance(e,urllib.error.HTTPError):
    r['status']=e.code
    if e.code in (403,429):DENIED.add(urllib.parse.urlparse(url).hostname)
 receipt.write_text(json.dumps(r,indent=2)+'\n');print(key,r.get('status'),r.get('error'),flush=True)
if __name__=='__main__':
 if len(sys.argv)>1:get(sys.argv[1],sys.argv[2])
 else:
  rows=json.loads((D/'extracted.json').read_text()); ids=sorted(set(x['source_url'].split('/')[-1] for x in rows.values()))
  for a in ids:get(a+'.abs','https://arxiv.org/abs/'+a)
  for repo in ['openai/math','Vilin97/lean-pool','the-omega-institute/trureturing']:
   key=repo.replace('/','-'); get(key+'-head.json','https://api.github.com/repos/'+repo+'/commits/HEAD')
   h=D/'sources'/(key+'-head.json')
   if h.exists():get(key+'-tree.json','https://api.github.com/repos/'+repo+'/git/trees/'+json.loads(h.read_text())['sha']+'?recursive=1')
