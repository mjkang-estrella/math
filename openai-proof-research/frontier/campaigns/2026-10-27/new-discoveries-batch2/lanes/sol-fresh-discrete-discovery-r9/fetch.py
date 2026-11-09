import urllib.request, urllib.error, hashlib, json, datetime, pathlib, resource, os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(45,45))
P=pathlib.Path(__file__).resolve().parent; receipts=[]; blocked=set()
items=[('source.html','https://arxiv.org/html/2410.23009v1'),('journal.html','https://link.springer.com/article/10.1007/s00029-026-01191-5'),('successor.html','https://arxiv.org/html/2504.05510v1'),('zhang.pdf','https://zenodo.org/records/23655610/files/ICLUE2026fromrep%20%2810%29%20%281%29.pdf?download=1')]
for name,url in items:
 host=urllib.request.urlparse(url).netloc if hasattr(urllib.request,'urlparse') else __import__('urllib.parse',fromlist=['urlparse']).urlparse(url).netloc
 r={'file':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 if host in blocked:r['skipped']='host blocked'
 else:
  try:
   with urllib.request.urlopen(url,timeout=25) as f: data=f.read(12*1024**2);r['status']=f.status
   if any(x in data[:10000].lower() for x in [b'cf-chl-',b'just a moment...',b'captcha']):blocked.add(host);r['error']='challenge';data=b''
   else:(P/'sources'/name).write_bytes(data);r.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
  except urllib.error.HTTPError as e:
   r['status']=e.code
   if e.code in (403,429):blocked.add(host)
  except Exception as e:r['error']=str(e)
 receipts.append(r)
(P/'fetch-receipts.json').write_text(json.dumps(receipts,indent=2));print(json.dumps(receipts,indent=2))
