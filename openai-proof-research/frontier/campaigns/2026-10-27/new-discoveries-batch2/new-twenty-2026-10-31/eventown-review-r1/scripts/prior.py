import urllib.request, pathlib,json,hashlib,datetime
urls={'furedi-list':'https://users.renyi.hu/~furedi/publ.html','harcos-abs':'https://arxiv.org/abs/1812.09225','furedi-doi':'https://doi.org/10.1137/090774835','search':'https://www.google.com/search?q=%22reverse-free+codes%22+%22pdf%22'}
for name,url in urls.items():
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=12) as f:
   b=f.read(10000000);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());pathlib.Path('receipts/'+name+'.body').write_bytes(b)
 except Exception as e:r['error']=str(e)
 pathlib.Path('receipts/'+name+'.json').write_text(json.dumps(r,indent=2));print(name,r,flush=True)
