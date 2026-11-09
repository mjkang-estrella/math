import urllib.request,datetime,hashlib,json,pathlib
W=pathlib.Path(__file__).resolve().parents[1]
urls={
'openai-head':'https://api.github.com/repos/openai/math/commits/HEAD',
'omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD',
'source-abs':'https://arxiv.org/abs/2106.06827',
'survey-abs':'https://arxiv.org/abs/2501.19385',
'products':'https://arxiv.org/html/2412.09837',
'digraphs':'https://arxiv.org/html/2604.15909',
'iteration':'https://arxiv.org/html/2305.00467'}
for key,url in urls.items():
 receipt={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'MathematicalReview/1.0'})
  with urllib.request.urlopen(req,timeout=15) as r:
   data=r.read();receipt.update(status=r.status,final_url=r.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());(W/'receipts'/(key+'.body')).write_bytes(data)
 except Exception as e:receipt['error']=str(e)
 (W/'receipts'/(key+'.json')).write_text(json.dumps(receipt,indent=2));print(key,receipt,flush=True)
