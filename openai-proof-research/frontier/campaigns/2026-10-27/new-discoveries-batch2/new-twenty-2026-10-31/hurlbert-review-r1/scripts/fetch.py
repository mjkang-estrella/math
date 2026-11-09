from pathlib import Path
import urllib.request,urllib.error,urllib.parse,json,hashlib,sys,datetime
D=Path(__file__).resolve().parents[1]; deniedfile=D/'denied-hosts.json'
denied=set(json.loads(deniedfile.read_text())) if deniedfile.exists() else set()
denied.update(['api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','sciencedirect.com','dblp.org','dblp.uni-trier.de'])
class NoRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,*args,**kw):return None
opener=urllib.request.build_opener(NoRedirect)
name,url=sys.argv[1:];dest=D/'downloads'/name;dest.mkdir(exist_ok=False)
records=[]
for step in range(6):
 host=urllib.parse.urlsplit(url).hostname
 if host in denied: records.append({'url':url,'blocked_locally':'previous denial or prohibited service'});break
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  try:r=opener.open(urllib.request.Request(url,headers={'User-Agent':'IndependentMathReview/1.0'}),timeout=22)
  except urllib.error.HTTPError as e:r=e
  body=r.read(15000000);rec.update(status=r.code,headers=dict(r.headers),sha256=hashlib.sha256(body).hexdigest(),bytes=len(body))
  (dest/f'body-{step}').write_bytes(body)
  if r.code in (403,429) or b'Just a moment...' in body or b'cf-chl-' in body:
   denied.add(host);rec['denied']=True;records.append(rec);break
  records.append(rec)
  if r.code in (301,302,303,307,308):url=urllib.parse.urljoin(url,r.headers['Location']);continue
  break
 except Exception as e:rec['error']=str(e);records.append(rec);break
(dest/'receipt.json').write_text(json.dumps(records,indent=2)+'\n');deniedfile.write_text(json.dumps(sorted(denied),indent=2)+'\n');print(name,json.dumps(records))
