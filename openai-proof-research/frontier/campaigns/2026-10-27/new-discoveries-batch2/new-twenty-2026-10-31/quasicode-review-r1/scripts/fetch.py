import urllib.request,urllib.error,pathlib,sys,json,datetime,hashlib
L=pathlib.Path(__file__).resolve().parents[1]
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 receipt={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Math research review; public-source verification'}),timeout=25) as r:
   data=r.read(15000000);receipt.update(status=r.status,final_url=r.url,headers=dict(r.headers),sha256=hashlib.sha256(data).hexdigest());(L/'receipts'/name).write_bytes(data)
 except Exception as e:receipt['error']=str(e)
 (L/'receipts'/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n');print(receipt.get('status'),name,receipt.get('error',''),flush=True)
