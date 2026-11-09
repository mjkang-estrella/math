"""Explore smaller target-32 trees; pickle checkpoints are search state, not nd certificates."""
import sys
sys.dont_write_bytecode=True
import os,json,time,signal,pickle,gc
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
C=__import__('continue');HERE=C.HERE
def main():
    gc.disable();summ=[]
    for profile in (sys.argv[1:] or ['compact','reorder']):
        start=time.monotonic()
        G=C.FastGen([9]*4,89,3,C.run_target.SUP,False,maxp=10**12)
        G.node_limit=2000000;G.account={'lifts':0,'max_lifts':500000000}
        if profile.startswith('tail'):G.lean=True
        if profile.endswith('cheap'):G.branch_policy='cheap'
        def timeout(*_):raise C.breadth.Budget('wall time')
        signal.signal(signal.SIGALRM,timeout);signal.setitimer(signal.ITIMER_REAL,300)
        try:
            sched=C.PROFILES[profile][0]
            ns,info,st=C.gen_hd.run(G,sched,workers=1,max_nodes=2000000,cap_level=2000000,budget_s=300)
            signal.setitimer(signal.ITIMER_REAL,0)
            rec={'profile':profile,'status':st,'frontiers':info,'nodes':len(ns) if ns else None,
                 'certificate_lifts':sum((v['m2']//v['m'])**G.dim for v in ns.values() if v['k']=='i') if ns else None,
                 'lifts':G.account['lifts'],'seconds':time.monotonic()-start}
            if ns is not None:
                p=os.path.join(HERE,f'opt32_{profile}.pickle')
                with open(p+'.tmp','wb') as f:pickle.dump({'nodes':ns,'schedule':sched,'stats':rec},f)
                os.replace(p+'.tmp',p)
        except (C.breadth.Budget,C.gen_hd.NodeBudgetExceeded,MemoryError) as ex:
            rec={'profile':profile,'status':str(ex),'lifts':G.account['lifts'],'seconds':time.monotonic()-start}
        finally:signal.setitimer(signal.ITIMER_REAL,0)
        summ.append(rec);C.breadth.atomic_json(os.path.join(HERE,'opt32_summary.json'),summ)
        print(json.dumps(rec),flush=True)
if __name__=='__main__':main()
