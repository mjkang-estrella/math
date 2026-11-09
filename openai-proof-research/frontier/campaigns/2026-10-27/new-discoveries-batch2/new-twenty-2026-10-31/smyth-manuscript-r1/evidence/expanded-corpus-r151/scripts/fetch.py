import urllib.request,hashlib,json,datetime,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1]
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Math-research-source-review/1.0'}),timeout=25) as r:
   b=r.read();rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(D/'sources'/f'{name}.body').write_bytes(b)
 except Exception as e: rec.update(error=str(e),status=getattr(e,'code',None))
 (D/'sources'/f'{name}.receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(name,rec)
