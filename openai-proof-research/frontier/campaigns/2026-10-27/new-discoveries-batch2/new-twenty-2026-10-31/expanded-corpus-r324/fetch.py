import urllib.request,datetime
urls=sys.argv[2:]
(P/'http').mkdir(exist_ok=True)
for url in urls:
 stamp=datetime.datetime.now(datetime.timezone.utc).isoformat(); key=hashlib.sha256(url.encode()).hexdigest()[:16]
 receipt=dict(url=url,utc=stamp,read_depth='retrieval only')
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'ordinary-math-research/1.0'}),timeout=22) as r:
   b=r.read(12*1024**2+1);assert len(b)<=12*1024**2
   (P/'http'/key).write_bytes(b);receipt.update(status=r.status,final_url=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),file='http/'+key)
 except Exception as e:receipt.update(error=str(e),status=getattr(e,'code',None))
 with (P/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
 print(json.dumps(receipt))
