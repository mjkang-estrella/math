import urllib.request,json,datetime,hashlib,pathlib
items=[('zinn.html','https://mathoverflow.net/questions/208349/zinns-doubling-conjecture-on-weighted-sums-of-independent-rademacher-random-v'),('pinelis.html','https://mathoverflow.net/users/36721/iosif-pinelis'),('jekl-followup.pdf','https://files.ele-math.com/articles/mia-28-42.pdf')]
with open('http.jsonl','a') as log:
 for name,url in items:
  r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'file':'sources/'+name}
  try:
   with urllib.request.urlopen(url,timeout=25) as f:b=f.read();r.update(status=f.status,headers=dict(f.headers))
   pathlib.Path(r['file']).write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  except Exception as e:r['error']=str(e)
  log.write(json.dumps(r)+'\n');log.flush()
