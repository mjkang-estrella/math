import os,resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,datetime,urllib.request,concurrent.futures,sys
L=pathlib.Path(__file__).resolve().parent
start=time.monotonic(); reads=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def write(n,b):
 p=(L/n).resolve(); assert p.is_relative_to(L); p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(b if isinstance(b,bytes) else b.encode())
def dump(n,o):write(n,json.dumps(o,ensure_ascii=False,indent=2)+'\n')
def read(p):
 p=pathlib.Path(p); assert not any(x in str(p).lower() for x in ['crown','transitive-bunkbed-formal-pi-r2']); b=p.read_bytes(); reads.append({'path':str(p),'bytes':len(b),'sha256':sha(b)}); return b
reservation=read(L/'reservation.json'); assert sha(reservation)=='4309f659f8cd448e92e3e5427531437d39f7759e52dff0053a18ddbb49adc639'
dump('reservation-before.json',{'sha256':sha(reservation),'expected_match':True,'sidecar':read(L/'reservation.sha256').decode()})
r=json.loads(reservation); ids=set(r['ids']); found={}
base=L.parent.parent
for p in sorted((base/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 b=read(p); ch=sha(b)
 for line,raw in enumerate(b.splitlines(keepends=True),1):
  obj=json.loads(raw); mid=obj.get('mathdb_id',obj.get('id'))
  if mid in ids or str(mid) in {str(x) for x in ids}:
   mid=int(mid); assert mid not in found
   write(f'literal/{mid}.jsonl',raw); dump(f'literal/{mid}.parsed.json',obj)
   found[mid]={'chunk':str(p),'line':line,'chunk_sha256':ch,'raw_sha256':sha(raw),'newline':raw.endswith(b'\n'),'parsed_record':obj}
assert set(found)==ids, (set(found),ids)
for mid,v in found.items():
 print(mid,json.dumps(v['parsed_record'],ensure_ascii=False))
 # discover statement key without altering text
 v['statement_field_hashes']={k:sha(val.encode()) for k,val in v['parsed_record'].items() if isinstance(val,str) and ('statement' in k or k in ['content','body','description'])}
dump('literal-provenance.json',found)
# read exact historical allowlist; no recursive historical scans
allow=json.loads(read(L/'historical-results-allowlist.json')); dump('allowlist-copy.json',allow)
print('ALLOWLIST',json.dumps(allow))
for p in [base/'ledger.json',L.parent/'ledger.json',L.parent/'STATUS.md']:
 if p.exists():
  if p.suffix=='.json':
   o=json.loads(read(p)); print('SCALARS',p,{k:o[k] for k in ['accepted_new','target'] if k in o})
  else:
   b=read(p); print('STATUS scalar only retained in inventory')
dump('read-inventory-initial.json',reads)
dump('resource-extract.json',{'exit':0,'wall_seconds':time.monotonic()-start,'affinity':sorted(os.sched_getaffinity(0)),'rusage_self':list(resource.getrusage(resource.RUSAGE_SELF)),'limits':{'cpu':120,'as':6*1024**3},'telemetry_limit':'self peak only; not concurrent cgroup peak'})
