"""Isolated checkpointed odd-index continuation; only standard nd certificates."""
import sys
sys.dont_write_bytecode=True
import os,json,time,signal,multiprocessing as mp,collections,hashlib,shutil,argparse,traceback,itertools
HERE=os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0,HERE)
import breadth,gen_hd,run_target
from hnt import vp
if os.path.exists(os.path.join(HERE,'supply_extended.json')):run_target.SUP=json.load(open(os.path.join(HERE,'supply_extended.json')))
from optimize import FastGen
class BudgetFastGen(breadth.BudgetGen,FastGen):pass
breadth.BudgetGen=BudgetFastGen
ROOT=os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
BASE=json.load(open(os.path.join(HERE,'baseline.json')))
SHARE=json.load(open(os.path.join(HERE,'share.json')))['keys']
SCHEDULES={
 'old':[2,3,7,3,2,2,2,3,5],
 'old_no5':[2,3,7,3,2,2,2,3],
 'three':[2,3,3,2,2,3,5,7],
 'two':[2,2,2,3,3,3,5,7],
 'short':[2,3,3,2,2],
 'minimal':[2,3],
 'rich2':[2,3,2,2,2,3,3,2,5,7],
 'ord22':[2,11,3,2,3,2,2,3,5,7],
 'ord13':[13,2,3,2,3,2,2,3,5,7],
 'five':[2,3,5,3,2,2,3,7],
 'eleven':[2,3,2,11,3,2,3,5,7],
}

def work(arg):
 key,stage,seconds,nodes,lifts,schedname,mcap,depth,probe,cheap,*extra=arg
 richness=extra[0] if extra else ""
 factors=extra[1] if len(extra)>1 else ""
 v=BASE[key]; S=v['S_low']; far=v['far']; start=time.monotonic()
 outdir=os.path.join(HERE,'logs',stage);os.makedirs(outdir,exist_ok=True)
 log=open(os.path.join(outdir,key.replace('|','_').replace(',','_')+'.log'),'w',buffering=1)
 olderr=sys.stderr;sys.stderr=log
 account={'lifts':0,'max_lifts':lifts}; records=[]; sols=[];stop=None; jobs=[]
 def alarm(s,f):raise breadth.Budget('wall time')
 oldh=signal.signal(signal.SIGALRM,alarm);signal.setitimer(signal.ITIMER_REAL,seconds)
 try:
  jobs=breadth.jobs_for(14112,S,far)
  if probe:jobs=jobs[:1]
  for K,coefs,qmin,ordered,fn in jobs:
   rec={'K':K,'coefs':list(coefs),'qmin':qmin,'domain':'ordered' if ordered else 'unordered','file':os.path.relpath(fn,HERE)}
   cached=breadth.existing_cert((K,coefs,qmin,ordered,fn))
   if cached:
    count,ss=cached;rec.update(status='closed',info={'nodes':count,'cached':True});records.append(rec)
    sols += [[K,list(coefs),s] for s in ss];continue
   sched=SCHEDULES[schedname] if len(coefs)>=3 else run_target.SCHED.get(len(coefs)+1,run_target.SCHED[5])[0]
   G=breadth.BudgetGen(coefs,K,qmin,run_target.SUP,ordered,maxp=10**12);G.account=account
   if cheap:G.candidate_factors=(2,3)
   if richness:G.richness=[tuple(map(int,z.split(":"))) for z in richness.split(",")]
   if factors:G.candidate_factors=tuple(map(int,factors.split(",")))
   try:
    ns,info,status=gen_hd.run(G,sched,workers=1,cap_level=nodes,max_nodes=nodes,mcap=mcap,maxdepthB=depth,budget_s=max(.01,seconds-(time.monotonic()-start)))
    last={'schedule':sched,'reason':status,'frontiers':info}
   except gen_hd.NodeBudgetExceeded as e:
    ns=None;last={'schedule':sched,'reason':str(e)}
   if ns is None:
    rec.update(status='BUDGET',info=last);records.append(rec);stop=last['reason'];break
   signal.setitimer(signal.ITIMER_REAL,0)
   tmpfn=fn+'.'+str(os.getpid())+'.tmp'
   gen_hd.write_cert(tmpfn,G,ns,{'sched':sched,'maxp':10**12,'stage':stage,'mcap':mcap,'maxdepthB':depth})
   os.replace(tmpfn,fn)
   rec.update(status='closed',info={'nodes':len(ns),'schedule':sched});records.append(rec)
   sols += [[K,list(coefs),list(s)] for s in gen_hd.solutions(ns)]
   remain=seconds-(time.monotonic()-start)
   if remain<=0:raise breadth.Budget('wall time after write')
   signal.setitimer(signal.ITIMER_REAL,remain)
 except (breadth.Budget,gen_hd.NodeBudgetExceeded,MemoryError,RecursionError) as ex:stop=f'{type(ex).__name__}: {ex}'
 except Exception:stop='ERROR';traceback.print_exc(file=log)
 finally:
  try:
   signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,oldh)
  except breadth.Budget:
   stop='Budget: wall time during teardown';signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,oldh)
  sys.stderr=olderr;log.close()
 diag={"phaseB":getattr(locals().get("G"),"diagnostic",None),"last_expansion":getattr(locals().get("G"),"current",None)}
 closed=len(records)==len(jobs) and all(r['status']=='closed' for r in records)
 result={'status':'CLOSED' if closed and not probe else 'PROBE_CLOSED' if closed else 'ERROR' if stop=='ERROR' else 'BUDGET',
 'S_low':S,'far':far,'multiset':v['multiset'],'slices':v['slices'],'certs':v['certs'],'jobs':records,'pending_jobs':len(jobs)-len(records),'stop_reason':stop,
 'sz_solutions':sorted(sols),'elapsed_s':round(time.monotonic()-start,3),'lifts_attempted':account['lifts'],'stage':stage,
 'budget':{'seconds':seconds,'nodes_per_attempt':nodes,'lifts_per_config':lifts,'mcap':mcap,'maxdepthB':depth},'schedule_name':schedname,'diagnostic':diag,'cheap':cheap}
 return key,result

def main():
 p=argparse.ArgumentParser();p.add_argument('stage');p.add_argument('--seconds',type=float,default=300);p.add_argument('--nodes',type=int,default=2000000);p.add_argument('--lifts',type=int,default=100000000);p.add_argument('--schedule',choices=SCHEDULES,default='three');p.add_argument('--mcap',type=int,default=10**18);p.add_argument('--depth',type=int,default=80);p.add_argument('--workers',type=int,default=12);p.add_argument('--limit',type=int,default=999);p.add_argument('--probe',action='store_true');p.add_argument('--keys');p.add_argument('--maxdim',type=int,default=99);p.add_argument('--mindim',type=int,default=1);p.add_argument('--offset',type=int,default=0)
 p.add_argument('--cheap',action='store_true')
 p.add_argument('--richness',default='')
 p.add_argument('--factors',default='')
 a=p.parse_args();assert 1<=a.workers<=12
 fn=os.path.join(HERE,'results_t14112.json');results=json.load(open(fn)) if os.path.exists(fn) else {}
 stagefn=os.path.join(HERE,'stage_'+a.stage+'.json');stage=json.load(open(stagefn)) if os.path.exists(stagefn) else {}
 keys=json.load(open(a.keys)) if a.keys else SHARE
 todo=[k for k in keys if results.get(k,{}).get('status')!='CLOSED' and k not in stage and a.mindim<=len(BASE[k]['far'])+1<=a.maxdim]
 todo.sort(key=lambda k:(len(BASE[k]['far']),BASE[k]['certs'],k));todo=todo[a.offset:][:a.limit]
 print('START',a.stage,len(todo),a,flush=True)
 with mp.get_context('fork').Pool(a.workers,maxtasksperchild=1) as pool:
  args=[(k,a.stage,a.seconds,a.nodes,a.lifts,a.schedule,a.mcap,a.depth,a.probe,a.cheap,a.richness,a.factors) for k in todo]
  for i,(key,r) in enumerate(pool.imap_unordered(work,args,chunksize=1),1):
   stage[key]=r;breadth.atomic_json(stagefn,stage)
   if not a.probe:
    results[key]=r;breadth.atomic_json(fn,results)
   print(i,'/',len(todo),key,r['status'],len(r['jobs']),'/',r['certs'],r['elapsed_s'],'s',r['stop_reason'],flush=True)
 print('SUMMARY',dict(collections.Counter(v['status'] for v in stage.values())),flush=True)
if __name__=='__main__':main()
