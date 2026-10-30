import sys,pathlib,urllib.request,urllib.error,hashlib,json,datetime
L=pathlib.Path(__file__).resolve().parent
(L/'retrieved').mkdir(exist_ok=True)
name,url=sys.argv[1:]
assert not any(x in url.lower() for x in ['github','codeload','sciencedirect','google.'])
row={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'name':name}
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'ScholarlySourceReview/1.0'}),timeout=40) as r:
  b=r.read(12000001);assert len(b)<=12000000
  row.update(status=r.status,final_url=r.url,headers=dict(r.headers))
except urllib.error.HTTPError as e:
 b=e.read(1000000);row.update(status=e.code,error=str(e))
except Exception as e:
 b=b'';row.update(error=repr(e))
(L/'retrieved'/name).write_bytes(b)
row.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
with (L/'access.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
print(json.dumps({k:v for k,v in row.items() if k!='headers'}))
