import pathlib,urllib.request,urllib.error,datetime,hashlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1]
blocked={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org'}
for p in (D/'sources').glob('*.receipt.json'):
 r=json.loads(p.read_text())
 if r.get('status') in [403,429] or r.get('challenge'):blocked.add(urllib.parse.urlsplit(r['url']).hostname)
class Safe(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,hdrs,url):
  if urllib.parse.urlsplit(url).hostname in blocked:raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,hdrs,url)
def get(key,url):
 p=D/'sources'/key; rec=p.with_name(p.name+'.receipt.json')
 if rec.exists():return
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  if urllib.parse.urlsplit(url).hostname in blocked:raise RuntimeError('host denied')
  with urllib.request.build_opener(Safe()).open(urllib.request.Request(url,headers={'User-Agent':'Research verification'}),timeout=25) as f:
   b=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));p.open('xb').write(b)
 except urllib.error.HTTPError as e:
  b=e.read();p.open('xb').write(b);r.update(status=e.code,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if e.code in [403,429]:blocked.add(urllib.parse.urlsplit(url).hostname)
 except Exception as e:r['error']=str(e)
 rec.open('x').write(json.dumps(r,indent=2)+'\n');print(key,r.get('status',r.get('error')),flush=True)
if __name__=='__main__':
 if len(sys.argv)>1:get(sys.argv[1],sys.argv[2])
 else:
  for repo,key in [('Vilin97/lean-pool','leanpool'),('openai/math','openai'),('the-omega-institute/trureturing','omega')]:get(key+'-head.json','https://api.github.com/repos/'+repo+'/commits/HEAD')
  for a in sorted({x['source_url'].split('/')[-1] for x in json.loads((D/'extracted.json').read_text()).values()}):
   get(a+'-abs.html','https://arxiv.org/abs/'+a)
   get(a+'.pdf','https://arxiv.org/pdf/'+a)
