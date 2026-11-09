import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,datetime
L=pathlib.Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
def write(n,b):
 p=(L/n).resolve(); assert p.is_relative_to(L); p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(b if isinstance(b,bytes) else b.encode())
def js(n,v):write(n,json.dumps(v,indent=2,ensure_ascii=False)+'\n')
t=time.monotonic(); reservation=(L/'reservation.json').read_bytes(); assert H(reservation)=='ed4524d5212fec69c21dd4f90f62e2f6b8007f4758ee3d4fe1e73ae135629630'; R=json.loads(reservation); ids=set(R['ids']); assert len(ids)==20
C=L.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
found={}
for p in sorted(C.glob('mathdb-normalized-chunk-*.jsonl')):
 b=p.read_bytes(); ch=H(b)
 for i,line in enumerate(b.splitlines(keepends=True),1):
  r=json.loads(line); id=r.get('mathdb_id',r.get('id'))
  if id in ids:
   assert id not in found and line.endswith(b'\n'); write(f'literal/{id}.jsonl',line); js(f'literal/{id}.json',r)
   statement=r.get('statement',r.get('content','')); found[id]={'chunk_path':str(p),'one_based_line':i,'chunk_sha256':ch,'raw_sha256':H(line),'statement_sha256':H(statement.encode()),'statement_field':'statement' if 'statement' in r else 'content','full_parsed_record':r}
 if len(found)==20:break
assert set(found)==ids
js('provenance.json',found)
terms=['overpartition','unbordered','Wilmes','clique cover','copositive','Thue','Nivat','quasirandom','stack-sort','unimodal','quandle','secure domination','bipartite-graph product','Laplacian coefficient','defective list','zero-sum','Neumann','pentagon','total domination']
hist=[]; skipped=[]
for s in json.loads((L/'historical-results-allowlist.json').read_text()):
 if any(x in s.lower() for x in ['crown','tournament-upper-support','transitive-bunkbed-upper-support']):skipped.append(s);continue
 p=pathlib.Path(s)
 if not p.is_file():continue
 b=p.read_bytes(); text=b.decode(); hits=[x for x in terms if x.lower() in text.lower()]
 if any(str(i) in text for i in ids) or hits:
  hist.append({'path':s,'sha256':H(b),'terms':hits,'records':json.loads(b)})
js('history-matches.json',hist); js('history-scope.json',{'allowlist_only':True,'protected_filtered_before_open':skipped,'matching_files':len(hist),'worldwide_clearance':False})
for p in [L.parent/'ledger.json',L.parent/'STATUS.md',L.parents[1]/'ledger.json',L.parents[1]/'prior-campaign-context.json']:
 if p.is_file():
  text=p.read_text(); vals={}
  if p.suffix=='.json':
   j=json.loads(text)
   if isinstance(j,dict): vals={k:v for k,v in j.items() if k in ['accepted_count','accepted','target','target_count','count','current_count','campaign_target','new_accepted_count'] and isinstance(v,(int,float,str,bool))}
  else:
   import re
   vals={m.group(1):m.group(2) for m in re.finditer(r'^([A-Za-z_]+):\s*(\d+(?:/\d+)?)\s*$',text,re.M)}
  print('SCALARS',str(p),vals)
for id in R['ids']:
 print('\nID',id,json.dumps(found[id]['full_parsed_record'],ensure_ascii=False))
js('intake-receipt.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'wall_seconds':time.monotonic()-t,'exit':0,'affinity':sorted(os.sched_getaffinity(0)),'self_rusage':list(resource.getrusage(resource.RUSAGE_SELF)),'reservation_before':H(reservation),'literal_count':len(found),'telemetry':'self only, not concurrent group peak'})
