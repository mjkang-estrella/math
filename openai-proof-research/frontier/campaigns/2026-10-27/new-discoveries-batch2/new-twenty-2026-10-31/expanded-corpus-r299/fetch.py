import resource, os, pathlib, urllib.request, hashlib, json, datetime, concurrent.futures, subprocess
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
P=pathlib.Path(__file__).parent
def fetch(item):
 name,url=item
 rec={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'read_depth':'retrieved_not_yet_read'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source qualification'}),timeout=18) as r:
   data=r.read(16000001); assert len(data)<=16000000
   rec.update(status=r.status,final_url=r.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
   f=P/'sources'/name; f.write_bytes(data)
   if data.startswith(b'%PDF'):
    subprocess.run(['pdftotext','-layout',str(f),str(f)+'.txt'],check=True,timeout=18,capture_output=True)
 except Exception as e: rec['error']=str(e)
 return rec
if __name__=='__main__':
 import sys
 (P/'sources').mkdir(exist_ok=True)
 items=json.loads(pathlib.Path(sys.argv[1]).read_text())
 with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool: records=list(pool.map(fetch,items))
 with (P/'http-receipts.jsonl').open('a') as out:
  for r in records: out.write(json.dumps(r)+'\n');print(json.dumps(r))
