import sys,urllib.request,hashlib,json,datetime,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
key,url=sys.argv[1],sys.argv[2]; p=D/'sources'/key; now=datetime.datetime.now(datetime.timezone.utc).isoformat()
try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source verification'}),timeout=25) as r: data=r.read(); rec=dict(url=url,final_url=r.url,status=r.status,utc=now,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),path=str(p)); p.write_bytes(data)
except Exception as e: rec=dict(url=url,utc=now,error=str(e))
(D/'sources'/(key+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n'); print(rec.get('status',rec.get('error')),rec.get('bytes'))
