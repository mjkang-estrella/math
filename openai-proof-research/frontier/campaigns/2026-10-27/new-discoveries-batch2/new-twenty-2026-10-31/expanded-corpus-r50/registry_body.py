import requests,json,pathlib,hashlib,datetime,base64
p=pathlib.Path(__file__).resolve().parent;rout=[]
for name,sha in [('albright-proof','5a0f96f66bc72f0a2e12485d505fa763b19b61d6'),('albright-problem','c78ddf065c806de2eb0b9d5e819ce630e4b4b262')]:
 url='https://api.github.com/repos/the-omega-institute/trureturing/git/blobs/'+sha;r=requests.get(url,timeout=15);raw=r.content;(p/'sources'/f'{name}-blob.json').write_bytes(raw);e={'url':url,'status':r.status_code,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sha256':hashlib.sha256(raw).hexdigest()}
 if r.status_code==200:
  b=base64.b64decode(r.json()['content']);(p/'sources'/f'{name}.txt').write_bytes(b);e['decoded_sha256']=hashlib.sha256(b).hexdigest()
 rout.append(e)
(p/'registry-body-receipts.json').write_text(json.dumps(rout,indent=2))
