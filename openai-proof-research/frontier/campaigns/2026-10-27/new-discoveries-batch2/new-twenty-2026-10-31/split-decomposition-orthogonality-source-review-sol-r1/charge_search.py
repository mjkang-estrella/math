"""Documentary native-search precharge; invoke only under the assigned run.py."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(115,115))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,sys,hashlib,datetime,subprocess,fcntl
lane=Path(__file__).resolve().parent
assert Path.cwd().resolve()==lane,'Assigned lane cwd required'
assert len(sys.argv)==2,'Expected own persisted search-plan path'
planpath=(lane/sys.argv[1]).resolve();assert planpath.is_relative_to(lane) and planpath.is_file()
planbytes=planpath.read_bytes();plan=json.loads(planbytes)
queries=plan['queries'];assert isinstance(queries,list) and queries and all(isinstance(q,str) and q.strip() for q in queries)
with (lane/'search-charge.lock').open('a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 budgetpath=lane/'search-budget.json';before=json.loads(budgetpath.read_text())
 ledgerpath=lane/'search-charges.jsonl';prior=ledgerpath.read_text() if ledgerpath.exists() else ''
 charges=[json.loads(s) for s in prior.splitlines() if s]
 assert before['calls_used']==len(charges) and before['queries_used']==sum(len(x['queries']) for x in charges),'Live counter/charge continuity mismatch; preserve and stop, never repair history'
 digest=hashlib.sha256(planbytes).hexdigest();assert digest not in {x['plan_sha256'] for x in charges},'Plan already charged'
 after=dict(before);after['calls_used']+=1;after['queries_used']+=len(queries)
 assert after['calls_used']<=before['maximum_calls'] and after['queries_used']<=before['maximum_queries'],'Search budget exhausted'
 charge=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sequence=len(charges)+1,plan=str(planpath.relative_to(lane)),plan_sha256=digest,queries=queries,before=before,after=after)
 def write(name,text):
  r=subprocess.run([sys.executable,'-I','-B',str(lane/'write_lane.py'),name],input=text,text=True,capture_output=True)
  if r.returncode:raise RuntimeError({'writer_exit':r.returncode,'stderr':r.stderr})
 write('search-budget.json',json.dumps(after,indent=2)+'\n')
 write('search-charges.jsonl',prior+json.dumps(charge,sort_keys=True)+'\n')
 print(json.dumps({'charged':charge,'next':'Run exactly this native search once, immediately save the FULL actual response; no reset/refund or history edits.'}))
