import urllib.request,datetime,hashlib,json,pathlib
W=pathlib.Path(__file__).resolve().parents[1]
urls={'colouring':'https://arxiv.org/html/2408.13494','varieties':'https://arxiv.org/html/2504.19671','likelihood':'https://arxiv.org/html/2608.19467'}
for key,url in urls.items():
 receipt={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'MathematicalReview/1.0'})
  with urllib.request.urlopen(req,timeout=15) as r:
   data=r.read();receipt.update(status=r.status,final_url=r.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());(W/'receipts'/(key+'.body')).write_bytes(data)
 except Exception as e:receipt['error']=str(e)
 (W/'receipts'/(key+'.json')).write_text(json.dumps(receipt,indent=2));print(key,receipt,flush=True)
