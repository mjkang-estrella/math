import pathlib,json,urllib.request,urllib.error,hashlib,datetime,sys
D=pathlib.Path(__file__).resolve().parents[1]
blocked={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org'}
for p in (D/'sources').glob('*.receipt.json'):
 r=json.loads(p.read_text())
 if r.get('status') in [403,429] or r.get('challenge'): blocked.add(urllib.parse.urlsplit(r['url']).hostname)
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlsplit(newurl).hostname in blocked: raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
opener=urllib.request.build_opener(Redirect)
for key,url in json.loads(pathlib.Path(sys.argv[1]).read_text()):
 p=D/'sources'/key
 if p.exists() or p.with_suffix(p.suffix+'.receipt.json').exists():raise RuntimeError('refuse overwrite '+key)
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  if urllib.parse.urlsplit(url).hostname in blocked:raise RuntimeError('host denied; not attempted')
  try: response=opener.open(urllib.request.Request(url,headers={'User-Agent':'Research source check'}),timeout=20)
  except urllib.error.HTTPError as e: response=e
  with response as f: data=f.read();r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
  p.write_bytes(data);r.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  if r['status'] in [403,429]:blocked.add(urllib.parse.urlsplit(url).hostname)
 except Exception as e:r['error']=str(e)
 p.with_suffix(p.suffix+'.receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(key,r.get('status',r.get('error')),r.get('bytes'),flush=True)
