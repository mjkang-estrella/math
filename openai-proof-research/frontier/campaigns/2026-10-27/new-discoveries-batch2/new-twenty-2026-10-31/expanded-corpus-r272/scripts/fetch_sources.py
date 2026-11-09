from pathlib import Path
import resource,os,json,hashlib,datetime,concurrent.futures,urllib.request,re
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=Path(__file__).resolve().parents[1];s=p/'sources';s.mkdir(exist_ok=True)
rows=[json.loads(f.read_text()) for f in (p/'raw').glob('*.json')];urls=sorted(set(r['source_url'] for r in rows))
def fetch(url):
 name=url.split('/abs/')[1].replace('/','_');f=s/(name+'.abs.html');rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source reader'}),timeout=16) as h: data=h.read(1500000);rec.update(status=h.status,final_url=h.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));f.write_bytes(data)
 except Exception as e:rec['error']=str(e)
 (s/(name+'.abs.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:
 for r in ex.map(fetch,urls): print(json.dumps(r),flush=True)
