import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,urllib.request,concurrent.futures,datetime,time,sys
L=pathlib.Path(__file__).resolve().parent; t=time.monotonic(); receipts=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(n,x):
 p=(L/n).resolve(); assert p.is_relative_to(L); p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
r=json.loads((L/'reservation.json').read_text()); urls=[]
for row in r['rows']:
 a=row['source_url'].rsplit('/',1)[1]; urls.extend([(str(row['mathdb_id'])+'-abs',row['source_url']),(str(row['mathdb_id'])+'-html','https://arxiv.org/html/'+a)])
def fetch(v):
 name,url=v; rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'GET','read_depth':'acquired_only'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source review'}),timeout=12) as resp:
   b=resp.read(12*1024**2); rec.update(status=resp.status,final_url=resp.url,bytes=len(b),sha256=sha(b)); p=L/'sources'/ (name+'.html'); p.parent.mkdir(exist_ok=True); p.write_bytes(b); rec['file']=str(p.relative_to(L))
 except Exception as e:rec.update(error=str(e),status=getattr(e,'code',None))
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for rec in ex.map(fetch,urls):
  receipts.append(rec); dump('http-receipts-acquire.json',receipts)
# only explicit allowlisted completed files, protected-filter before reading
allow=json.loads((L/'historical-results-allowlist.json').read_text()); hist=[]; inventory=[]
for s in allow:
 if any(w in s.lower() for w in ['crown','transitive-bunkbed-formal-pi-r2']):continue
 p=pathlib.Path(s)
 if not p.is_file():continue
 b=p.read_bytes(); inventory.append({'path':s,'bytes':len(b),'sha256':sha(b)})
 txt=b.decode(errors='replace')
 matches=[str(mid) for mid in r['ids'] if str(mid) in txt]
 if matches: hist.append({'path':s,'id_hits':matches,'content':json.loads(txt)})
dump('history-matches.json',hist); dump('history-read-inventory.json',inventory)
dump('resource-acquire.json',{'exit':0,'wall_seconds':time.monotonic()-t,'self':list(resource.getrusage(resource.RUSAGE_SELF)),'threads':2,'affinity':sorted(os.sched_getaffinity(0)),'telemetry_limit':'self peak only, threads joined, no child processes'})
print('HTTP',[(x['url'],x.get('status'),x.get('bytes')) for x in receipts]); print('HISTORY',len(inventory),[(x['path'],x['id_hits']) for x in hist])
