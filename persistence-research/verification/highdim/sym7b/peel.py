#!/usr/bin/env python3
"""Adaptive position peeling. Search only; audit_peel.py replays coverage independently."""
import sys
sys.dont_write_bytecode=True
import argparse,collections,concurrent.futures,fcntl,hashlib,json,pathlib,shutil,signal,time
H=pathlib.Path(__file__).resolve().parent
R=H.parents[2]
sys.path.insert(0,str(H))
from gen_precomputed import PrecomputedGenerator
from gen_sym import Budget,valuation

def load(p): return json.loads(pathlib.Path(p).read_text())
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def save(p,v):
 p=pathlib.Path(p); t=p.with_suffix(p.suffix+'.tmp');t.write_text(json.dumps(v,indent=1)+'\n');t.replace(p)
def ident(K,cs,p): return '%d:%s:%d'%(K,','.join(map(str,cs)),p)
def state(K,cs,p): return {'K':K,'coefs':list(cs),'p':p,'status':'PENDING'}
def init():
 old=H.parent/'sym6'; summary=load(old/'summary.json'); assignment=load(old/'assignment.json')
 cfg={k:assignment['configurations'][k] for k in summary['open']}
 save(H/'assignment.json',{'configurations':cfg,'source':str(old/'summary.json'),'source_sha256':sha(old/'summary.json')})
 manifest={str(old/n):sha(old/n) for n in ('gen_sym.py','gen_precomputed.py','check_sym5.py','supply.json','audit_coverage.py','coverage_distinct.py','audit_orderings.py')}
 manifest.update({str(R/'verification/indep5'/n):sha(R/'verification/indep5'/n) for n in ('check_sym_F5.py','NOTE_F5.md')})
 save(H/'source_hashes.json',manifest)
 # Only use full certificates, taking their arithmetic on trust for SEARCH ONLY.
 # Every selected file is copied locally and freshly checked by both CLIs later.
 lib=collections.defaultdict(list)
 for stage in ('sym6','sym3'):
  ledger=load(H.parent/stage/'kill_usage.json')
  for f,r in ledger.items():
   m=r['meta']
   if m['scope']!='full': continue
   cs=tuple(c for c,n in m['groups'] for _ in range(n))
   lib[(m['K'],cs)].append({'qmin':m['qmin'],'file':f,'sha256':r['sha256']})
 save(H/'library.json',[{'K':K,'coefs':cs,'options':sorted(v,key=lambda r:(r['qmin'],pathlib.Path(r['file']).stat().st_size))} for (K,cs),v in lib.items()])
 roots={};states={}
 for key,r in cfg.items():
  K=9*r['S_low']-1; cs=tuple(sorted(r['far'])); i=ident(K,cs,3)
  roots[key]=i;states[i]=state(K,cs,3)
 save(H/'tree.json',{'roots':roots,'states':states,'runs':[]})
 print('initialized',len(cfg),'configurations,',len(lib),'library domains',flush=True)

def alarm(*_): raise Budget('wall alarm')
def work(arg):
 i,s,seconds,pin,lifts,schedule=arg
 signal.signal(signal.SIGALRM,alarm);signal.setitimer(signal.ITIMER_REAL,seconds)
 K,cs,p=s['K'],s['coefs'],s['p'];start=time.monotonic();g=None
 fn=H/'certs'/('K%d_q%d_c%s.jsonl'%(K,p,'_'.join(map(str,cs)) or 'none'))
 out={'id':i,'pin_digits':pin,'budget_seconds':seconds}
 try:
  g=PrecomputedGenerator(cs,K,p,seconds=seconds,lifts=lifts,nodes=500000,mcap=10**140,depth=400,pin_digits=pin)
  g.run(schedule)
  fn.parent.mkdir(exist_ok=True)
  g.write(fn,extra={'stage':'sym7b-adaptive-peeling'})
  out.update(result='CERTIFICATE',file=str(fn),sha256=sha(fn),solutions=g.solutions())
 except Exception as e:
  out.update(result='BUDGET' if isinstance(e,Budget) else 'ERROR',reason=repr(e))
 finally: signal.setitimer(signal.ITIMER_REAL,0)
 if g is not None: out.update(nodes=len(g.nodes),lifts=g.lifts,kills=dict(g.kills),trace=g.trace,at=g.at)
 out['seconds']=round(time.monotonic()-start,3)
 return out

def run(a):
 t=load(H/'tree.json');lib={(r['K'],tuple(r['coefs'])):r['options'] for r in load(H/'library.json')}
 states=t['states'];queue=[];copied=0;splits=0
 def expand(i,s):
  nonlocal splits
  K,cs,p=s['K'],tuple(s['coefs']),s['p']
  children={'empty':ident(K,cs,p+1)}
  states.setdefault(children['empty'],state(K,cs,p+1))
  for c in sorted(set(cs)):
   rest=list(cs);rest.remove(c);K1=K+c*10**p;ch=ident(K1,tuple(rest),p+1)
   children[str(c)]=ch;states.setdefault(ch,state(K1,rest,p+1))
  s.update(status='SPLIT',children=children);splits+=1
 # Expand all existing leaves to the stage floor. Never split a proved domain.
 if a.only_k or a.only_key:
  assigned=load(H/'assignment.json')['configurations'];todo=[];seen=set()
  pending=[root for key,root in t['roots'].items() if (not a.only_k or len(assigned[key]['far'])==a.only_k) and (not a.only_key or key==a.only_key)]
  while pending:
   i=pending.pop()
   if i in seen:continue
   seen.add(i);pending.extend(states[i].get('children',{}).values());todo.append(i)
 else:todo=list(states)
 while todo:
  i=todo.pop();s=states[i]
  if s['status'] not in ('PENDING','OPEN'): continue
  K,cs,p=s['K'],tuple(s['coefs']),s['p']
  opts=[v for v in lib.get((K,cs),[]) if v['qmin']<=p]
  if opts:
   src=pathlib.Path(min(opts,key=lambda v:pathlib.Path(v['file']).stat().st_size)['file']);h=sha(src)
   assert h in {v['sha256'] for v in opts if v['file']==str(src)}
   dst=H/'certs'/('inherited_'+h+'.jsonl');dst.parent.mkdir(exist_ok=True)
   if not dst.exists(): shutil.copyfile(src,dst);copied+=1
   s.update(status='CERTIFICATE',file=str(dst),sha256=h,inherited_from=str(src));continue
  if p<a.floor or p<=valuation(K,2):
   if p>=a.max_p:
    s['status']='OPEN';s['reason']='floor/v2 exceeds bounded peeling depth';continue
   expand(i,s);todo.extend(s['children'].values());continue
  if p>a.max_p: s['status']='OPEN';continue
  if not a.min_free<=len(cs)<=a.max_free: continue
  # Attempt exactly once per schedule/stage; resumed commands skip completed work.
  if s.get('attempts') and s['attempts'][-1].get('stage')==a.stage: continue
  queue.append((i,s,a.seconds,min(p,a.pin_cap),a.lifts,tuple(map(int,a.schedule.split(',')))))
 queue.sort(key=lambda job:(len(job[1]['coefs']),job[1]['p'],job[1]['K']))
 save(H/'tree.json',t)
 print('stage',a.stage,'states',len(states),'copied',copied,'forced splits',splits,'queued',len(queue),flush=True)
 start=time.monotonic();counts=collections.Counter();results=[]
 with concurrent.futures.ProcessPoolExecutor(max_workers=a.workers) as pool:
  for result in pool.map(work,queue,chunksize=1):
   i=result['id'];s=states[i];result['stage']=a.stage
   s.setdefault('attempts',[]).append(result);counts[result['result']]+=1;results.append(result)
   if result['result']=='CERTIFICATE': s.update(status='CERTIFICATE',file=result['file'],sha256=result['sha256'])
   elif s['p']<a.max_p:
    expand(i,s)
   else: s.update(status='OPEN',reason=result.get('reason','bounded search'))
   save(H/'tree.json',t)
   with (H/'search_journal.jsonl').open('a') as f:f.write(json.dumps(result)+'\n')
   print(a.stage,len(results),'/',len(queue),i,result['result'],result['seconds'],flush=True)
 t['runs'].append({'stage':a.stage,'counts':dict(counts),'seconds':round(time.monotonic()-start,3),'parameters':vars(a)})
 save(H/'tree.json',t);save(H/('search_'+a.stage+'.json'),results)
 print(dict(counts),'states',len(states),dict(collections.Counter(s['status'] for s in states.values())),flush=True)

if __name__=='__main__':
 ap=argparse.ArgumentParser();sp=ap.add_subparsers(dest='action',required=True);sp.add_parser('init');p=sp.add_parser('run')
 p.add_argument('--stage',required=True);p.add_argument('--floor',type=int,default=6);p.add_argument('--max-p',type=int,default=8)
 p.add_argument('--pin-cap',type=int,default=7);p.add_argument('--seconds',type=float,default=8);p.add_argument('--workers',type=int,default=6)
 p.add_argument('--lifts',type=int,default=15000000);p.add_argument('--schedule',default='2,3,5,2,3,2,7')
 p.add_argument('--min-free',type=int,default=0);p.add_argument('--max-free',type=int,default=99)
 p.add_argument('--only-k',type=int,default=0)
 p.add_argument('--only-key',default='')
 a=ap.parse_args()
 if a.action=='init':init()
 else:
  assert 1<=a.workers<=8
  with (H/'search.lock').open('a') as lock:
   fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
   run(a)
