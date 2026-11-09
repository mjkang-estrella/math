import urllib.request,urllib.error,json,hashlib,datetime,pathlib
base=pathlib.Path(__file__).resolve().parent
out=[]; blocked={'mathdb.com','api.github.com'}
for name,url in [('tian.html','https://arxiv.org/html/0910.1571v1'),('tian.pdf','https://arxiv.org/pdf/0910.1571v1'),('tian-abs.html','https://arxiv.org/abs/0910.1571'),('wehrung.pdf','https://wehrungf.users.lmno.cnrs.fr/fichiers/GAR17_Fred.pdf')]:
 host=urllib.parse.urlparse(url).hostname
 if host in blocked: continue
 r={'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=25) as f: data=f.read(4000000);r['status']=f.status
  if b'captcha' in data[:3000].lower() or b'challenge' in data[:3000].lower():
   blocked.add(host);r['challenge']=True
  else:
   (base/r['file']).write_bytes(data);r.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
 except urllib.error.HTTPError as e:
  r['status']=e.code
  if e.code in [403,429]:blocked.add(host)
 except Exception as e:r['error']=str(e)
 out.append(r)
(base/'retrievals.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
