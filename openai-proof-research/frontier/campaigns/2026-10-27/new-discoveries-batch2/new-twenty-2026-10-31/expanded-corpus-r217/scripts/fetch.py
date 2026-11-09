# usage: fetch.py LANE_DIR name1 url1 name2 url2 ...  ; never overwrites receipts; no retries
import urllib.request,urllib.error,hashlib,json,datetime,pathlib,sys,ssl,time
D=pathlib.Path(sys.argv[1]).resolve()/'sources'
DENY=['api.crossref.org','api.semanticscholar.org','export.arxiv.org/api','sciencedirect.com','dblp.org','dblp.uni-trier.de']
class NoRedirect(urllib.request.HTTPRedirectHandler):
  def redirect_request(self, req, fp, code, msg, hdrs, newurl):
    for d in DENY:
      if d in newurl: raise urllib.error.HTTPError(newurl, code, 'redirect to denied host blocked', hdrs, fp)
    return super().redirect_request(req, fp, code, msg, hdrs, newurl)
op=urllib.request.build_opener(NoRedirect, urllib.request.HTTPSHandler(context=ssl.create_default_context()))
args=sys.argv[2:]
for name,url in zip(args[0::2],args[1::2]):
  rp=D/f'{name}.receipt.json'
  if rp.exists(): print(name,'EXISTS-skip'); continue
  if any(d in url for d in DENY): print(name,'DENIED-host-skip'); continue
  rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
    with op.open(urllib.request.Request(url,headers={'User-Agent':'math-research-source-review/1.0'}),timeout=30) as r:
      b=r.read(); rec.update(status=r.status,final_url=r.url,content_type=r.headers.get('Content-Type'),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b)); (D/f'{name}.body').write_bytes(b)
  except Exception as e:
    rec.update(error=str(e)[:300],status=getattr(e,'code',None))
  rp.write_text(json.dumps(rec,indent=2)+'\n'); print(name,rec.get('status'),rec.get('bytes'),rec.get('error',''))
  time.sleep(1.5)
