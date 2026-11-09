import pathlib,urllib.request,urllib.parse,urllib.error,datetime,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1]; stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'); out=D/'sources'/('resume-'+stamp);out.mkdir()
denied=set(json.loads((D/'outputs/denied-hosts.json').read_text()))|{'dblp.org','dblp.dagstuhl.de','sciencedirect.com'}
class Guard(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,h,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied:raise RuntimeError('redirect denied '+newurl)
  return super().redirect_request(req,fp,code,msg,h,newurl)
urls={'mirror-v1':'https://arxiv.org/html/2202.13548v1','inversion-v2':'https://arxiv.org/html/2402.16251v2','betti-proof':'https://arxiv.org/html/2605.22808v1','vincular-proof':'https://arxiv.org/html/2509.13097v1','pgst-lean':'https://raw.githubusercontent.com/the-omega-institute/trureturing/a8f1af6c2a2679392be1d3fb660bd114452b1370/D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation.lean'}
for key,url in urls.items():
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url};p=out/(key+'.body')
 try:
  if urllib.parse.urlparse(url).hostname in denied:raise RuntimeError('denied host skipped')
  with urllib.request.build_opener(Guard()).open(urllib.request.Request(url,headers={'User-Agent':'Research/1.0'}),timeout=25) as h:b=h.read();r.update(status=h.status,final_url=h.url,headers=dict(h.headers))
  p.write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),path=str(p))
  if b'challenge-platform' in b or b'captcha' in b.lower()[:10000]:denied.add(urllib.parse.urlparse(url).hostname);r['challenge_detected']=True
 except urllib.error.HTTPError as e:
  b=e.read();p.write_bytes(b);r.update(status=e.code,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),error=str(e))
  if e.code in (403,429):denied.add(urllib.parse.urlparse(url).hostname)
 except Exception as e:r['error']=str(e)
 p.with_suffix('.body.receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(key,r.get('status'),r.get('error'),r.get('bytes'),flush=True)
(out/'denied.json').write_text(json.dumps(sorted(denied)));print(out)
