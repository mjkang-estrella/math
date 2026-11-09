import urllib.request,urllib.error,urllib.parse,json,datetime,hashlib,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1]; banned={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','api.arxiv.org','www.sciencedirect.com','sciencedirect.com','dblp.org','mathdb.com','palomar.mathdb.com'}
class NoRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,*a,**kw): return None
def get(key,url):
 p=D/'http'/key
 if p.exists() or pathlib.Path(str(p)+'.receipt.json').exists(): raise RuntimeError('Existing receipt '+key)
 deny=D/'http/denied.json'; denied=set(json.loads(deny.read_text())) if deny.exists() else set()
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'redirects':[]}
 data=b''
 try:
  for i in range(5):
   host=urllib.parse.urlparse(url).hostname
   if host in banned or host in denied: raise RuntimeError('Host denied; request not sent: '+host)
   try:
    r=urllib.request.build_opener(NoRedirect).open(urllib.request.Request(url,headers={'User-Agent':'Research source verification (read-only)'}),timeout=25)
   except urllib.error.HTTPError as e:r=e
   status=r.code; data=r.read(); headers=dict(r.headers);r.close()
   if status in (403,429) or b'bot challenge' in data[:20000].lower():
    denied.add(host);deny.write_text(json.dumps(sorted(denied)))
   if status in (301,302,303,307,308):
    rec['redirects'].append({'url':url,'status':status,'location':headers.get('Location')});url=urllib.parse.urljoin(url,headers['Location']);continue
   rec.update(status=status,final_url=url,headers=headers);break
  p.write_bytes(data);rec.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),path=str(p))
 except Exception as e:rec['error']=str(e)
 pathlib.Path(str(p)+'.receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(key,rec.get('status',rec.get('error')),len(data),flush=True);return rec
if __name__=='__main__':get(sys.argv[1],sys.argv[2])
