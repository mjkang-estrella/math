import urllib.request,pathlib,json,hashlib,datetime,time
D=json.load(open('outputs/extracted.json')); receipts=[]
urls={v['record']['source_url'].rsplit('/',1)[-1] for v in D.values()}
for a in sorted(urls):
 u='https://arxiv.org/pdf/'+a
 p=pathlib.Path('sources')/(a+'.pdf')
 try:
  r=urllib.request.urlopen(u,timeout=15); data=r.read(); p.write_bytes(data); s=r.status
 except Exception as e: data=b''; s=str(e)
 receipts.append(dict(url=u,status=s,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=hashlib.sha256(data).hexdigest() if data else None))
 json.dump(receipts,open('outputs/http.json','w'),indent=2); print(a,s,len(data),flush=True)
