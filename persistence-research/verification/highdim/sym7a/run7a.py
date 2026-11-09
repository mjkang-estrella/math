#!/usr/bin/env python3
"""Adaptive exhaustive position peeling; all outputs live in sym7a."""
import sys
sys.dont_write_bytecode=True
import argparse,collections,concurrent.futures,hashlib,json,pathlib,signal,time,multiprocessing,os
H=pathlib.Path(__file__).resolve().parent
R=H.parents[2]
sys.path.insert(0,str(H))
from gen_sym import Budget,valuation
from gen_precomputed import PrecomputedGenerator

def read(p): return json.loads(pathlib.Path(p).read_text())
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def save(p,o):
 p=pathlib.Path(p);t=p.with_suffix(p.suffix+'.tmp');t.write_text(json.dumps(o,indent=1)+'\n');t.replace(p)
def ident(K,cs,p): return '%s:%s:%s'%(K,','.join(map(str,cs)),p)
def alarm(*_): raise Budget('slice wall alarm')
LIB={}
def setup():
 global LIB
 s=read(H.parent/'sym5/summary.json');a=read(H.parent/'sym5/assignment.json')['configurations']
 jobs={k:{x:a[k][x] for x in ('S_low','far','target','key')} for k in s['open']}
 assert len(jobs)==33
 save(H/'assignment.json',{'source':str(H.parent/'sym5/summary.json'),'source_sha256':sha(H.parent/'sym5/summary.json'),'configurations':jobs})
 checks=read(H.parent/'sym5/checks5.json')['files'];n=0
 for f,rec in checks.items():
  if rec.get('M',{}).get('result')!='PASS': continue
  p=pathlib.Path(f)
  with p.open() as stream:m=json.loads(next(stream))
  if m['scope']!='full':continue
  cs=tuple(c for c,n in m['groups'] for _ in range(n))
  assert sha(p)==rec['M']['sha256']
  LIB.setdefault((m['K'],cs),[]).append((m['qmin'],f))
 for p in sorted((H/'certs').glob('*.jsonl')):
  m=json.loads(p.open().readline());cs=tuple(c for c,n in m['groups'] for _ in range(n))
  LIB.setdefault((m['K'],cs),[]).append((m['qmin'],str(p)))
 for key in LIB:LIB[key].sort()
 return jobs

def worker(args):
 name,rec,stage,target,seconds,slice_seconds,schedule,rich_five=args
 signal.signal(signal.SIGALRM,alarm)
 start=time.monotonic();todo=[(9*rec['S_low']-1,tuple(sorted(rec['far'])),3)];nodes={};attempts=[];used={}
 while todo and time.monotonic()-start<seconds:
  K,cs,p=todo.pop();key=ident(K,cs,p)
  if key in nodes:continue
  node={'K':K,'coefs':cs,'qmin':p,'t0':valuation(K,2)};nodes[key]=node
  opts=[(q,f) for q,f in LIB.get((K,cs),[]) if q<=p]
  if opts:
   q,f=opts[0];node.update(kind='certificate',file=f);used[f]={'cached':True};continue
  valid=p>valuation(K,2)
  fn=H/'certs'/('K%d_q%d_c%s.jsonl'%(K,p,'_'.join(map(str,cs)) or 'none'))
  # Expensive high-dimensional low-floor attempts are deferred until the pin is deep.
  try_now=valid and (p>=target or len(cs)<=4)
  if try_now:
   g=None;st=time.monotonic()
   try:
    limit=min(slice_seconds,max(.01,seconds-(st-start)))
    signal.setitimer(signal.ITIMER_REAL,limit)
    g=PrecomputedGenerator(cs,K,p,seconds=limit,lifts=5000000,nodes=100000,mcap=10**140,depth=450,pin_digits=min(p,target))
    if rich_five:g.refinement_cycle=(2,3,5,2,3,5,2,7)
    g.run(schedule)
    pending=fn.with_suffix('.pending.'+str(os.getpid()))
    g.write(pending,extra={'stage':stage,'configuration':name,'peeling':True})
    try:os.link(pending,fn)
    except FileExistsError:pass
    pending.unlink()
    node.update(kind='certificate',file=str(fn));used[str(fn)]={'cached':False}
   except (Budget,MemoryError,AssertionError) as e:
    attempts.append({'state':key,'reason':repr(e),'seconds':round(time.monotonic()-st,4),'nodes':len(g.nodes) if g else 0,'lifts':g.lifts if g else 0,'at':g.at if g else None})
   finally:signal.setitimer(signal.ITIMER_REAL,0)
   if node.get('kind')=='certificate':continue
  if p>=target and valid:
   node['kind']='open';continue
  # At most one occupant at p. Most frequent group is considered first.
  order=sorted(collections.Counter(cs),key=lambda c:(-cs.count(c),c))
  children=[(K,cs,p+1)]
  for c in order:
   rest=list(cs);rest.remove(c);children.append((K+c*10**p,tuple(rest),p+1))
  node.update(kind='peel',order=order,children=[ident(*z) for z in children])
  todo.extend(reversed(children))
 for K,cs,p in todo:
  key=ident(K,cs,p)
  nodes.setdefault(key,{'K':K,'coefs':cs,'qmin':p,'t0':valuation(K,2),'kind':'open','reason':'configuration wall budget'})
 out={'name':name,'stage':stage,'target_floor':target,'seconds':round(time.monotonic()-start,3),'nodes':nodes,'attempts':attempts,'used':used,'status':'CANDIDATE' if all(n['kind']!='open' for n in nodes.values()) else 'OPEN'}
 save(H/('tree_'+stage+'_'+hashlib.sha256(name.encode()).hexdigest()[:16]+'.json'),out)
 return {k:v for k,v in out.items() if k not in ('nodes','attempts','used')}|{'states':len(nodes),'certificates':len(used),'attempts':len(attempts),'open_leaves':sum(n['kind']=='open' for n in nodes.values())}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--stage',default='peel7');ap.add_argument('--floor',type=int,default=7);ap.add_argument('--seconds',type=float,default=90);ap.add_argument('--slice-seconds',type=float,default=2);ap.add_argument('--workers',type=int,default=8);ap.add_argument('--schedule',default='2,3,5,2,3,2,7');ap.add_argument('--key');ap.add_argument('--rich-five',action='store_true');a=ap.parse_args()
 jobs=setup();save(H/('input_'+a.stage+'.json'),vars(a))
 path=H/('search_'+a.stage+'.json');results=read(path) if path.exists() else {}
 tasks=[(k,r,a.stage,a.floor,a.seconds,a.slice_seconds,tuple(map(int,a.schedule.split(','))),a.rich_five) for k,r in sorted(jobs.items(),key=lambda z:(len(z[1]['far']),z[0])) if k not in results and (not a.key or k==a.key)]
 with concurrent.futures.ProcessPoolExecutor(max_workers=a.workers,mp_context=multiprocessing.get_context('fork')) as ex:
  for r in ex.map(worker,tasks):
   results[r['name']]=r;save(path,results);print(json.dumps(r),flush=True)
if __name__=='__main__':main()
