import urllib.request,urllib.error,pathlib,hashlib,json,datetime
urls={
 'arxiv-current':'https://arxiv.org/abs/2601.12613',
 'arxiv-body':'https://arxiv.org/html/2601.12613',
 'openai-HEAD':'https://api.github.com/repos/openai/math/commits/HEAD',
 'omega-HEAD':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD',
 'ellis':'https://arxiv.org/html/1106.0725',
 'lindzey-matrix':'https://arxiv.org/html/2606.12380',
 'lindzey-other':'https://arxiv.org/html/2606.22697',
 'citing-multiset':'https://arxiv.org/html/2610.21636',
}
for name,url in urls.items():
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Independent-mathematical-review/1.0'}),timeout=12) as f:
   b=f.read(12000000);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());pathlib.Path('receipts/'+name+'.body').write_bytes(b)
 except Exception as e:r['error']=str(e)
 pathlib.Path('receipts/'+name+'.json').write_text(json.dumps(r,indent=2));print(name,r,flush=True)
