import pathlib,urllib.request,urllib.error,hashlib,datetime,json,sys
D=pathlib.Path(__file__).resolve().parents[1]
for name,url in [tuple(a.split('=',1)) for a in sys.argv[1:]]:
 r={'url':url,'date':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathDB-independent-review/1.0'}),timeout=25) as f:
   b=f.read();r.update(status=f.status,final_url=f.url,headers=dict(f.headers),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(D/'prior'/name).write_bytes(b)
 except Exception as e:r['error']=str(e)
 (D/'receipts'/('http-'+name+'.json')).write_text(json.dumps(r,indent=2));print(name,r.get('status'),r.get('error'),r.get('bytes'))
