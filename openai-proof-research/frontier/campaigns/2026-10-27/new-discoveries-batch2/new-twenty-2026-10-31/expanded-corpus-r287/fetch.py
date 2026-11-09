import urllib.request,urllib.error,pathlib,json,hashlib,datetime,sys,concurrent.futures
p=pathlib.Path(__file__).parent;(p/'http').mkdir(exist_ok=True)
def fetch(item):
 name,url=item; r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=18) as h: data=h.read(12000000);r.update(status=h.status,final_url=h.url)
 except urllib.error.HTTPError as e: data=e.read(200000);r.update(status=e.code,error=str(e))
 except Exception as e: data=b'';r.update(status=None,error=str(e))
 (p/'http'/name).write_bytes(data);r.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest());return r
items=json.loads(sys.stdin.read())
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(fetch,items):
  with (p/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r['name'],r['status'],r['bytes'])
