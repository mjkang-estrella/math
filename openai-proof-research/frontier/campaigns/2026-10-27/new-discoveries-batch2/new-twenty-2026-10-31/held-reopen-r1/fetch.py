import sys,pathlib,json,urllib.request,urllib.error,urllib.parse,hashlib,datetime
L=pathlib.Path(__file__).parent
old=json.loads((L/'prior-routes.json').read_text())
seen={r['receipt'].get('url') for r in old}
log=L/'http-receipts.jsonl'
if log.exists():
 seen.update(json.loads(s)['url'] for s in log.read_text().splitlines())
banned=['sciencedirect.com','springer.com','hal.science','epub.jku.at','sfb-qmc.jku.at','crossref.org','semanticscholar.org','fatcat.wiki','scholar.archive.org','citeseerx','mathdb','palmar','palomar','ieeexplore','export.arxiv.org']
def deny(u):
 return any(s in urllib.parse.urlparse(u).netloc for s in banned)
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if deny(newurl) or newurl in seen: raise RuntimeError('redirect refused: '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
for u in sys.argv[1:]:
 if deny(u) or u in seen:
  print('SKIP known/excluded',u); continue
 d=L/'downloads'/('request-'+str(len(list((L/'downloads').iterdir()))+1).zfill(3));d.mkdir()
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':u,'directory':str(d.relative_to(L))}
 seen.add(u)
 try:
  op=urllib.request.build_opener(Redirect())
  try: response=op.open(urllib.request.Request(u,headers={'User-Agent':'Academic-source-review/1.0'}),timeout=18)
  except urllib.error.HTTPError as e: response=e
  with response as f:
   r.update(status=f.status,final_url=f.url,headers=dict(f.headers));b=f.read(20*1024*1024+1)
   if len(b)>20*1024*1024: raise RuntimeError('size cap')
   (d/'body').write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
   r['challenge']=any(s in b[:50000].lower() for s in [b'anubis',b'cf-chl-',b'session verification',b'proof-of-work'])
 except Exception as e:r['error']=str(e)
 with log.open('a') as f:f.write(json.dumps(r)+'\n')
 print(json.dumps({k:v for k,v in r.items() if k not in ['headers']}),flush=True)
