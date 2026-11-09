import sys,os,json,hashlib,urllib.request,urllib.error,datetime,ssl,urllib.parse
DENY=('sciencedirect.com','linkinghub.elsevier.com','elsevier.com','crossref.org','semanticscholar.org','export.arxiv.org','springer.com','worldscientific.com')
class R(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        h=urllib.parse.urlparse(newurl).hostname or ''
        if any(h==d or h.endswith('.'+d) for d in DENY): raise urllib.error.HTTPError(newurl,code,'blocked redirect to denied host '+h,headers,fp)
        return super().redirect_request(req, fp, code, msg, headers, newurl)
url,outroot=sys.argv[1],sys.argv[2]
h=urllib.parse.urlparse(url).hostname or ''
assert not any(h==d or h.endswith('.'+d) for d in DENY)
ts=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
d=os.path.join(outroot,ts); os.makedirs(d)  # fresh, must not exist
op=urllib.request.build_opener(R(),urllib.request.HTTPSHandler(context=ssl.create_default_context()))
req=urllib.request.Request(url,headers={'User-Agent':'math-research-root-check/1.0'})
rec={'url':url,'utc':ts}
try:
    r=op.open(req,timeout=40); body=r.read(20_000_000); rec.update(status=r.status,final_url=r.geturl(),content_type=r.headers.get('Content-Type'))
except urllib.error.HTTPError as e:
    body=e.read() if hasattr(e,'read') and e.fp else b''; rec.update(status=e.code,error=str(e.msg))
except Exception as e:
    body=b''; rec.update(status=None,error=repr(e))
open(os.path.join(d,'body'),'xb').write(body)
rec['sha256']=hashlib.sha256(body).hexdigest(); rec['bytes']=len(body)
open(os.path.join(d,'receipt.json'),'x').write(json.dumps(rec,indent=1))
print(json.dumps(rec)); print(d)
