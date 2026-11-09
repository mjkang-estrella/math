import pathlib,urllib.request,urllib.error,urllib.parse,json,hashlib,time,sys
D=pathlib.Path(__file__).resolve().parents[1]
DENIED={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org'}
class NoRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,*a,**k): return None
def fetch(url,label):
 stamp=str(time.time_ns()); base=D/'http'/f'{stamp}-{label}'; rec={'url':url,'utc_ns':stamp}
 op=urllib.request.build_opener(NoRedirect)
 try:
  for step in range(6):
   host=urllib.parse.urlsplit(url).hostname
   if host in DENIED: raise RuntimeError('denied host '+host)
   try:r=op.open(urllib.request.Request(url,headers={'User-Agent':'Research literature audit contact-free/1.0'}),timeout=25)
   except urllib.error.HTTPError as e:r=e
   b=r.read(); p=pathlib.Path(str(base)+f'-{step}.body');p.write_bytes(b)
   rec.setdefault('steps',[]).append({'url':url,'status':r.code,'headers':dict(r.headers),'file':str(p.relative_to(D)),'sha256':hashlib.sha256(b).hexdigest()})
   if r.code in (403,429) or b'Just a moment' in b[:10000] or b'captcha' in b[:2000].lower(): DENIED.add(host);break
   if r.code in (301,302,303,307,308):url=urllib.parse.urljoin(url,r.headers['Location']);continue
   break
 except Exception as e:rec['error']=repr(e)
 pathlib.Path(str(base)+'.receipt.json').write_text(json.dumps(rec,indent=2))
 print(label,[(s['status'],s['file']) for s in rec.get('steps',[])],rec.get('error',''),flush=True)
 return rec
if __name__=='__main__':
 for l in sys.stdin:
  label,url=l.strip().split(' ',1);fetch(url,label)
