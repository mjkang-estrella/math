import pathlib,urllib.request,urllib.error,urllib.parse,json,hashlib,datetime,sys
L=pathlib.Path(__file__).resolve().parents[1]
class NoRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,*a,**kw):return None
op=urllib.request.build_opener(NoRedirect)
def fetch(url,label):
 host=urllib.parse.urlparse(url).hostname
 for prior in (L/'sources').glob('*/receipt.json'):
  old=json.loads(prior.read_text())
  if old.get('status') in [403,429] and urllib.parse.urlparse(old.get('url','')).hostname==host:raise SystemExit('Host previously denied: '+host)
 d=L/'sources'/label;d.mkdir(exist_ok=False)
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=op.open(urllib.request.Request(url,headers={'User-Agent':'Mathematical-research/1.0'}),timeout=22); b=r.read(); rec.update(status=r.status,headers=dict(r.headers));(d/'body').write_bytes(b);rec.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except urllib.error.HTTPError as e:
  b=e.read();(d/'body').write_bytes(b);rec.update(status=e.code,headers=dict(e.headers),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:rec['error']=str(e)
 (d/'receipt.json').write_text(json.dumps(rec,indent=2));print(label,rec.get('status',rec.get('error')),flush=True)
 if rec.get('status') in [403,429]:raise SystemExit('Denied; stop without retry')
if __name__=='__main__':
 for url,label in json.loads(pathlib.Path(sys.argv[1]).read_text()):fetch(url,label)
