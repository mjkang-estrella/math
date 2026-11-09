#!/usr/bin/env python3
"""Bounded experiment driver; all writes remain inside sym/. Max 12 workers."""
import argparse
import collections
import concurrent.futures
import functools
import hashlib
import json
import math
import os
import pathlib
import signal
import sys
import time
sys.dont_write_bytecode=True
HERE=pathlib.Path(__file__).resolve().parent
HD=HERE.parent
sys.path.insert(0,str(HERE))
from gen_sym import Generator,Budget,valuation
from check_sym import Checker
from project_nd import project


def save(path,obj):
    path=pathlib.Path(path)
    path.parent.mkdir(parents=True,exist_ok=True)
    tmp=path.with_suffix(path.suffix+'.tmp')
    tmp.write_text(json.dumps(obj,indent=1)+'\n'); tmp.replace(path)


def slices(K0,coefs,limit=200000):
    # Exhaustive branch cover. At every step a coordinate is fixed at one of its
    # finitely many low positions or is raised beyond v2(K). Dropping unequal
    # floors at the end enlarges each emitted domain and is safe.
    todo=[(K0,tuple(sorted(coefs)),(3,)*len(coefs))]
    seen=set(); result=set()
    while todo:
        K,cs,floors=todo.pop()
        state=(K,cs,floors)
        if state in seen: continue
        seen.add(state)
        if len(seen)>limit: raise Budget('slice enumeration')
        t=valuation(K,2)
        bad=next((i for i,x in enumerate(floors) if x<=t),None)
        if bad is None:
            result.add((K,cs,max(3,t+1)))
            continue
        i=bad
        for q in range(floors[i],t+1):
            todo.append((K+cs[i]*10**q,cs[:i]+cs[i+1:],floors[:i]+floors[i+1:]))
        todo.append((K,cs,floors[:i]+(t+1,)+floors[i+1:]))
    return sorted(result)


def timeout_handler(signum,frame): raise Budget('wall alarm')


def check_file(path,brute=10):
    return Checker(path,brute).run()


@functools.lru_cache(None)
def legacy_library():
    index={}
    ledger=HERE/'cross_all.json'
    if not ledger.exists(): return index
    for rec in json.loads(ledger.read_text()).values():
        if rec['status']!='CLOSED': continue
        check=rec['check']
        cs=tuple(c for c,n in check['groups'] for _ in range(n))
        p=pathlib.Path(rec['certificate'])
        with p.open() as f: meta=json.loads(next(f))
        index[(check['K'],cs,meta['qmin'])]=rec
    return index


def cross_worker(args):
    source,seconds=args
    signal.signal(signal.SIGALRM,timeout_handler)
    signal.setitimer(signal.ITIMER_REAL,seconds)
    start=time.monotonic()
    rel=pathlib.Path(source).relative_to(HD)
    dest=HERE/'crosscheck'/rel
    try:
        result=project(source,dest,seconds)
        result['check']=check_file(dest,10)
        result['status']='CLOSED'
        result['sha256']=hashlib.sha256(dest.read_bytes()).hexdigest()
    except Exception as e:
        result={'source':str(source),'status':'BUDGET' if isinstance(e,Budget) else 'FAIL',
                'error':repr(e)}
    finally: signal.setitimer(signal.ITIMER_REAL,0)
    result['seconds']=round(time.monotonic()-start,3)
    return result


def attack_worker(args):
    key,rec,seconds,liftcap,schedule,stage=args
    signal.signal(signal.SIGALRM,timeout_handler)
    signal.setitimer(signal.ITIMER_REAL,seconds)
    start=time.monotonic()
    result={'key':key,'dim':len(rec['far'])+1,'far':rec['far'],'S_low':rec['S_low'],
            'label':'COMPUTED','status':'BUDGET','stage':stage,'jobs':[]}
    g=None
    try:
        sl=slices(9*rec['S_low']-1,rec['far'])
        result['slice_count']=len(sl)
        result['finite_Lmax']=max(q-1 for K,cs,q in sl)
        # Hardest slices first: an incomplete cover is never reported CLOSED.
        sl.sort(key=lambda z:(-len(z[1]),z[0]))
        for K,cs,q in sl:
            cached=legacy_library().get((K,cs,q))
            if cached:
                fp=pathlib.Path(cached['certificate'])
                assert hashlib.sha256(fp.read_bytes()).hexdigest()==cached['sha256']
                result['jobs'].append({'K':K,'coefs':cs,'qmin':q,'file':str(fp.relative_to(HERE)),
                                       'check':cached['check'],'cached_legacy':True,'sha256':cached['sha256']})
                continue
            fn=HERE/'certs'/stage/f'K{K}_q{q}_c{"_".join(map(str,cs)) or "none"}.jsonl'
            if fn.exists():
                check=check_file(fn,10)
                result['jobs'].append({'K':K,'coefs':cs,'qmin':q,'file':str(fn.relative_to(HERE)),
                                       'check':check,'cached':True})
                continue
            remain=seconds-(time.monotonic()-start)
            if remain<0.1: raise Budget('configuration time')
            g=Generator(cs,K,q,seconds=remain,lifts=liftcap,nodes=800000,sumsets=True)
            g.run(schedule)
            g.write(fn,extra={'target':14112,'configuration':key,'stage':stage})
            check=check_file(fn,10)
            result['jobs'].append({'K':K,'coefs':cs,'qmin':q,'file':str(fn.relative_to(HERE)),
                                   'check':check,'nodes':len(g.nodes),'lifts':g.lifts,
                                   'trace':g.trace,'sha256':hashlib.sha256(fn.read_bytes()).hexdigest()})
        result['status']='SLICE_COVER_CHECKED'
        result['label']='PROVED'
    except Exception as e:
        result['reason']=repr(e)
        if not isinstance(e,Budget): result['status']='FAIL'
        if g is not None:
            result['partial']={'nodes':len(g.nodes),'lifts':g.lifts,'trace':g.trace,'at':g.at,
                               'sumset_kills':dict(g.kills)}
    finally: signal.setitimer(signal.ITIMER_REAL,0)
    result['seconds']=round(time.monotonic()-start,3)
    return result


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('mode',choices=['cross','attack'])
    ap.add_argument('--seconds',type=float,default=60)
    ap.add_argument('--lifts',type=int,default=10000000)
    ap.add_argument('--workers',type=int,default=12)
    ap.add_argument('--stage',default='broad')
    ap.add_argument('--limit',type=int)
    ap.add_argument('--schedule',default='2,3,7,3,2,2,2,3')
    ap.add_argument('--key')
    ap.add_argument('--retry-budget',action='store_true')
    ap.add_argument('--only-unclosed',action='store_true')
    ap.add_argument('--mindim',type=int,default=6)
    ap.add_argument('--maxdim',type=int,default=8)
    args=ap.parse_args()
    assert 1<=args.workers<=12
    if args.mode=='cross':
        sources=list((HD/'codex/certs').rglob('*.jsonl'))+list((HD/'certs/t112').glob('*.jsonl'))
        # Equivalent orderings need one new unordered cover, but retain the source map.
        unique={}
        for f in sorted(sources):
            with f.open() as stream: m=json.loads(next(stream))
            k=(m['K'],tuple(sorted(m['coefs'])),m['qmin'])
            unique.setdefault(k,[]).append(str(f))
        source_map={'label':'COMPUTED','source_count':len(sources),'unique_domains':len(unique),
                    'domains':[{'K':k[0],'coefs':k[1],'qmin':k[2],'sources':v} for k,v in unique.items()]}
        save(HERE/'crosscheck_sources.json',source_map)
        jobs=[(v[0],args.seconds) for v in unique.values()]
        worker=cross_worker
    else:
        sources=[HD/'codex/results_t14112.json',HD/'codex3b/results_t14112.json',HD/'codex3a/results_t14112.json']
        baseline=json.loads(sources[0].read_text())
        shared={}
        for path in sources:
            d=json.loads(path.read_text())
            save(HERE/'inputs'/args.stage/path.parent.name/path.name,d)
            for k,v in d.items():
                if v['status']=='CLOSED': shared[k]=str(path)
        cfgs=[(k,v) for k,v in baseline.items() if v['status']=='BUDGET' and args.mindim<=len(v['far'])+1<=args.maxdim]
        cfgs.sort(key=lambda kv:(kv[1].get('slices',99999),-max(collections.Counter(kv[1]['far']).values()),len(kv[1]['far']),kv[0]))
        if args.key: cfgs=[(k,v) for k,v in cfgs if k in args.key.split(';')]
        sched=tuple(int(x) for x in args.schedule.split(',') if x)
        jobs=[(k,v,args.seconds,args.lifts,sched,args.stage) for k,v in cfgs]
        if args.only_unclosed:
            covered=set()
            for previous in HERE.glob('attack_*.json'):
                for k,v in json.loads(previous.read_text()).items():
                    if v['status']=='SLICE_COVER_CHECKED': covered.add(k)
            jobs=[j for j in jobs if j[0] not in covered]
        save(HERE/f'input_{args.stage}.json',{'label':'COMPUTED','keys':[k for k,v in cfgs],
              'counts':dict(collections.Counter(len(v['far'])+1 for k,v in cfgs)),
              'already_closed_elsewhere':shared,'schedule':sched,
              'sources':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
              'code_sha256':{name:hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                             for name in ('gen_sym.py','check_sym.py','run_experiments.py')}})
        for name in ('gen_sym.py','check_sym.py','run_experiments.py'):
            path=HERE/'inputs'/args.stage/name
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes((HERE/name).read_bytes())
        worker=attack_worker
    if args.limit is not None: jobs=jobs[:args.limit]
    path=HERE/f'{args.mode}_{args.stage}.json'
    results=json.loads(path.read_text()) if path.exists() else {}
    if args.retry_budget:
        results={k:v for k,v in results.items() if v['status'] in ('CLOSED','SLICE_COVER_CHECKED')}
    jobs=[j for j in jobs if str(j[0]) not in results]
    print('jobs',len(jobs),'workers',args.workers,flush=True)
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        pending={pool.submit(worker,job):str(job[0]) for job in jobs}
        for fut in concurrent.futures.as_completed(pending):
            key=pending[fut]
            try: result=fut.result()
            except Exception as e: result={'status':'FAIL','error':repr(e)}
            results[key]=result
            save(path,results)
            print(key,result['status'],result.get('seconds'),len(results),'/',len(pending),flush=True)
    print('counts',dict(collections.Counter(v['status'] for v in results.values())),flush=True)

if __name__=='__main__': main()
