import os,resource
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,30))
import urllib.request,urllib.error,json,hashlib,datetime,pathlib
P=pathlib.Path(__file__).resolve().parent;receipt=[];blocked={'api.github.com','mathdb.com'}
for name,url in [('current-source.html','https://arxiv.org/abs/2410.23009'),('current-zhang.json','https://zenodo.org/api/records/23655610')]:
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url};host=__import__('urllib.parse',fromlist=['urlparse']).urlparse(url).netloc
 if host in blocked:r['skipped']='existing access limit'
 else:
  try:
   with urllib.request.urlopen(url,timeout=20) as f:body=f.read(4*1024**2+1);r['status']=f.status
   assert len(body)<=4*1024**2
   if any(t in body[:20000].lower() for t in [b'cf-chl-',b'just a moment...',b'captcha']):blocked.add(host);r['error']='challenge; no more affected-host requests'
   else:(P/'sources'/name).write_bytes(body);r.update(file=name,bytes=len(body),sha256=hashlib.sha256(body).hexdigest())
  except urllib.error.HTTPError as e:
   r['status']=e.code
   if e.code in [403,429]:blocked.add(host)
  except Exception as e:r['error']=str(e)
 receipt.append(r)
(P/'fetch-receipts.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
