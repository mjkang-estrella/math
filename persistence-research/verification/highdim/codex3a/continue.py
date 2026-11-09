"""Checkpointed 3a-only search. Python stdlib; explicit full residue trees."""
import sys
sys.dont_write_bytecode=True
import os,json,time,itertools,math,multiprocessing as mp,signal,traceback,gc
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
import breadth,gen_hd,run_target
HERE=breadth.HERE
extra=os.path.join(HERE,'supply_scan.json')
if os.path.exists(extra):
    run_target.SUP += [row[:4] for row in json.load(open(extra))['new_primes']]

class FastGen(breadth.BudgetGen):
    """Search acceleration only. Equal-coefficient stabilizers preserve every test.
    Output still lists all labelled children, so both original checkers replay it.
    """
    def __init__(self,*args,**kw):
        super().__init__(*args,**kw)
        self.pc={};self.inv={};self.cache_entries=0
        self.ec={};self.ecsize=0;self.ecM=None
        self.level_new=0;self.node_limit=2000000
    def before_level(self,frontier_count,f):
        super().before_level(frontier_count,f)
        self.level_new=0
    def test(self,e,r,a,w):
        p,d,o3,o7,H,pw,cw,i2=e
        if pw is None:
            T=(pow(10,r[0]%d,p)+self.K+sum(c*pow(10,x%d,p) for c,x in zip(self.coefs,r[1:])))*i2%p
        else:
            T=(pw[r[0]%d]+self.K+sum(cw[i][r[i+1]%d] for i in range(self.dim-1)))*i2%p
        if not T:return True
        au,wu=a[1] is None,w[1] is None
        h=H if au and wu else o3 if au else o7 if wu else 1
        if h==p-1:return False
        # Lower powers of an unbounded generator do not change subgroup membership.
        if not au:
            key=(3,a[0],p)
            if key not in self.inv:self.inv[key]=pow(3,-a[0],p)
            T=T*self.inv[key]%p
        if not wu:
            key=(7,w[0],p)
            if key not in self.inv:self.inv[key]=pow(7,-w[0],p)
            T=T*self.inv[key]%p
        if h==1:return T!=1
        key=(p,h)
        cache=self.pc.setdefault(key,{})
        if T not in cache:
            ans=pow(T,h,p)!=1
            if self.cache_entries<1000000:
                cache[T]=ans;self.cache_entries+=1
            return ans
        return cache[T]
    def expand(self,r,M,f):
        cost=f**self.dim
        if self.account['lifts']+cost>self.account['max_lifts']:raise breadth.Budget('lift cap')
        self.account['lifts']+=cost
        groups={}
        for i,c in enumerate(self.coefs,1):groups.setdefault(c,[]).append(i)
        # A permutation between equal coefficients is an automorphism of X.
        order=list(range(self.dim))
        for g in groups.values():
            for i,j in zip(g,sorted(g,key=lambda j:r[j])):order[i]=j
        canonical=tuple(r[j] for j in order);key=(canonical,f)
        if self.ecM!=M or self.ecsize>300000 or len(self.ec)>20000:
            self.ec={};self.ecsize=0;self.ecM=M
        if key not in self.ec:
            self.ec[key]=self.expand_core(canonical,M,f)
            self.ecsize+=len(self.ec[key][0])
        alive,used=self.ec[key]
        if getattr(self,'_phaseA',False):
            self.level_new+=len(alive)
            if self.current_nodes+self.level_new>self.node_limit:
                raise gen_hd.NodeBudgetExceeded(f'node cap {self.node_limit} (streamed level)')
        if order==list(range(self.dim)):return alive,used
        out=[]
        for rr,a,w in alive:
            dest=[0]*self.dim
            for i,j in enumerate(order):dest[j]=rr[i]
            out.append((tuple(dest),a,w))
        return out,used
    def expand_core(self,r,M,f):
        groups={}
        for i,c in enumerate(self.coefs,1):groups.setdefault((c,r[i]),[]).append(i)
        groups=list(groups.values())
        choices=[list(itertools.combinations_with_replacement(range(f),len(g))) for g in groups]
        alive=[];used=[];M2=M*f
        for t0 in range(f):
            for vals in itertools.product(*choices):
                rr=[r[0]+t0*M]+list(r[1:])
                for g,vs in zip(groups,vals):
                    for i,v in zip(g,vs):rr[i]+=v*M
                rr=tuple(rr);a,w=self.sig(rr,M2)
                e=self.kill(rr,M2,a,w,used)
                if e is not None:
                    if e not in used:used.append(e)
                    continue
                # Restore every labelled lift in the orbit; no quotient in certificate.
                perms=[sorted(set(itertools.permutations(vs))) for vs in vals]
                for perm in itertools.product(*perms):
                    r2=[r[0]+t0*M]+list(r[1:])
                    for g,vs in zip(groups,perm):
                        for i,v in zip(g,vs):r2[i]+=v*M
                    alive.append((tuple(r2),a,w))
                    if getattr(self,'_phaseA',False) and self.current_nodes+self.level_new+len(alive)>self.node_limit:
                        raise gen_hd.NodeBudgetExceeded(f'node cap {self.node_limit} (streamed parent)')
        return alive,used

PROFILES={
 'early2':[[2,2,2,3,2,3,5,7]],
 'early5':[[2,3,5,2,2,2,3,7]],
 'baseline':[[2,3,7,3,2,2,2,3,5]],
 'deep':[[2,2,2,3,2,3,5,7],[2,3,5,2,2,2,3,7],[2,3,7,3,2,2,2,3,5]],
 'early11':[[2,3,2,11,2,2,3,5,7]],
 'branch':[[2,3,2,2,2,3,5]],
 'early3':[[3,2,3,2,2,2,5,7]],
 'power2':[[2,3,2,2,2,2,2,2,2,2,3,5,7]],
 'reorder':[[2,3,7,2,3,2,2,3,5]],
 'local':[[2,3,2,2,2]],
 'greedy':[[2,3,7,3,2,2,2,3,5]],
 'compact':[[2,3,2,5,2,2,3,7]],
 'early9':[[3,3,2,2,2,2,5,7,3]],
 'tail252':[[2,3,7,3,2]],
 'tail1008':[[2,3,7,3,2,2,2]],
 'tail720':[[2,2,2,3,2,3,5]],
 'tail504cheap':[[2,3,7,3,2,2]],
}

def work(arg):
    # Each worker handles one configuration and then exits; avoid repeated full
    # cyclic-GC scans of the large acyclic residue tree and expansion caches.
    gc.disable()
    t,key,detail,seconds,nodes,lifts,profile,mcap=arg
    S=detail['S_low'];far=detail['far'];start=time.monotonic()
    logdir=os.path.join(HERE,'logs',profile,f't{t}');os.makedirs(logdir,exist_ok=True)
    log=open(os.path.join(logdir,key.replace('|','_').replace(',','_')+'.log'),'w',buffering=1)
    olderr=sys.stderr;sys.stderr=log
    account={'lifts':0,'max_lifts':lifts};records=[];sols=[];stop=None
    jobs=breadth.jobs_for(t,S,far)
    def timeout(*_):raise breadth.Budget('wall time')
    signal.signal(signal.SIGALRM,timeout);signal.setitimer(signal.ITIMER_REAL,seconds)
    try:
        for job in jobs:
            K,coefs,qmin,ordered,fn=job
            rec={'K':K,'coefs':list(coefs),'qmin':qmin,'domain':'ordered' if ordered else 'unordered','file':os.path.relpath(fn,HERE)}
            cached=breadth.existing_cert(job)
            if cached:
                n,ss=cached;rec.update(status='closed',info={'nodes':n,'cached':True});records.append(rec)
                sols += [[K,list(coefs),s] for s in ss];continue
            schedules=PROFILES[profile] if len(coefs)>=3 else run_target.SCHED[len(coefs)+1]
            for sched in schedules:
                G=FastGen(coefs,K,qmin,run_target.SUP,ordered,maxp=10**12);G.account=account
                G.node_limit=nodes
                if profile=='greedy':G.branch_policy='greedy'
                if profile.startswith('tail'):G.lean=True
                if profile.endswith('cheap'):G.branch_policy='cheap'
                try:
                    ns,info,st=gen_hd.run(G,sched,workers=1,cap_level=nodes,max_nodes=nodes,
                        mcap=mcap,maxdepthB=100,budget_s=max(.01,seconds-(time.monotonic()-start)))
                    last={'schedule':sched,'reason':st,'frontiers':info}
                except gen_hd.NodeBudgetExceeded as ex:
                    ns=None;last={'schedule':sched,'reason':str(ex)}
                if ns is not None:
                    signal.setitimer(signal.ITIMER_REAL,0)
                    gen_hd.write_cert(fn+'.tmp',G,ns,{'sched':sched,'maxp':10**12,'mcap':mcap,'search':'codex3a FastGen explicit labelled orbits'})
                    os.replace(fn+'.tmp',fn)
                    rec.update(status='closed',info={'nodes':len(ns),'schedule':sched});records.append(rec)
                    sols += [[K,list(coefs),list(s)] for s in gen_hd.solutions(ns)]
                    if time.monotonic()-start>=seconds:raise breadth.Budget('wall time after write')
                    signal.setitimer(signal.ITIMER_REAL,seconds-(time.monotonic()-start));break
            else:
                rec.update(status='BUDGET',info=last);records.append(rec);stop=last['reason'];break
    except (breadth.Budget,gen_hd.NodeBudgetExceeded,MemoryError,RecursionError) as ex:stop=f'{type(ex).__name__}: {ex}'
    except Exception:
        stop='ERROR';traceback.print_exc(file=log)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0);sys.stderr=olderr;log.close()
    closed=len(records)==len(jobs) and all(r['status']=='closed' for r in records)
    return key,{'multiset':detail['multiset'],'S_low':S,'far':far,'status':'CLOSED' if closed else 'ERROR' if stop=='ERROR' else 'BUDGET',
        'slices':len(run_target.slices(9*S-1,far)),'certs':len(jobs),'jobs':records,'pending_jobs':len(jobs)-len(records),
        'sz_solutions':sorted(sols),'budget':{'seconds':seconds,'nodes':nodes,'lifts':lifts,'profile':profile,'mcap':mcap},
        'elapsed_s':round(time.monotonic()-start,3),'lifts_attempted':account['lifts'],'stop_reason':stop}

def main():
    t=int(sys.argv[1]);profile=sys.argv[2];seconds=float(sys.argv[3]);nodes=int(sys.argv[4]);lifts=int(sys.argv[5])
    start=int(sys.argv[6]);end=int(sys.argv[7]);workers=int(sys.argv[8]) if len(sys.argv)>8 else 12
    mcap=int(sys.argv[9]) if len(sys.argv)>9 else 10**12
    assert 1<=workers<=12
    incoming=json.load(open(os.path.join(HERE,f'incoming_t{t}.json')))
    resfn=os.path.join(HERE,f'results_t{t}.json')
    results=json.load(open(resfn)) if os.path.exists(resfn) else {}
    keys=sorted(incoming)[start:end]
    if '--key-file' in sys.argv:
        selected=json.load(open(os.path.join(HERE,sys.argv[sys.argv.index('--key-file')+1])))
        assert set(selected)<=set(keys)
        keys=selected
    todo=[(t,k,incoming[k],seconds,nodes,lifts,profile,mcap) for k in keys if results.get(k,{}).get('status')!='CLOSED']
    if '--once' in sys.argv:
        attempted=set()
        histfn=os.path.join(HERE,'history.jsonl')
        if os.path.exists(histfn):
            for line in open(histfn):
                h=json.loads(line);b=h['result']['budget']
                if h['target']==t and b.get('profile')==profile and b.get('seconds')==seconds and b.get('nodes')==nodes and b.get('lifts')==lifts and b.get('mcap')==mcap:
                    attempted.add(h['key'])
        todo=[a for a in todo if a[1] not in attempted]
    if '--unattempted' in sys.argv:
        attempted={json.loads(line)['key'] for line in open(os.path.join(HERE,'history.jsonl')) if json.loads(line)['target']==t}
        todo=[a for a in todo if a[1] not in attempted]
    todo.sort(key=lambda a:(len(a[2]['far']),a[1]))
    print('START',t,profile,'range',start,end,'todo',len(todo),flush=True)
    hist=os.path.join(HERE,'history.jsonl')
    with mp.get_context('fork').Pool(workers,maxtasksperchild=1) as pool:
        for i,(k,r) in enumerate(pool.imap_unordered(work,todo,chunksize=1),1):
            results[k]=r;breadth.atomic_json(resfn,results)
            with open(hist,'a') as f:f.write(json.dumps({'target':t,'key':k,'result':r})+'\n')
            print(i,k,r['status'],r['elapsed_s'],r['lifts_attempted'],r['stop_reason'],flush=True)
    print('SUMMARY',{s:sum(r['status']==s for r in results.values()) for s in ('CLOSED','BUDGET','ERROR')},flush=True)

if __name__=='__main__':main()
