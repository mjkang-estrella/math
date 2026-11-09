import sys
sys.dont_write_bytecode = True
import os, json, signal, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_hd, run_target
from breadth import BudgetGen, Budget
cases = [([9,9,9],89), ([54,72,72],5723), ([9,9,9,9],89)]
for c,K in cases:
    G = BudgetGen(c,K,max(3,gen_hd.vp(K,2)+1),run_target.SUP,False,maxp=10**12)
    G.account = {'lifts':0,'max_lifts':10000000}
    start=time.monotonic()
    def stop(s,f): raise Budget('time')
    signal.signal(signal.SIGALRM,stop); signal.alarm(90)
    try:
        ns,info,status=gen_hd.run(G,[2,3,7,3,2,2,2,3,5],workers=1,max_nodes=600000)
        if ns:
            fn=os.path.join(os.path.dirname(__file__),'certs',f'probe_K{K}_u'+ '_'.join(map(str,c))+'.jsonl')
            gen_hd.write_cert(fn,G,ns,{'probe':True})
        print(c,K,status,'nodes',len(ns) if ns else None,'lifts',G.account['lifts'],'seconds',time.monotonic()-start,flush=True)
    except (Budget,gen_hd.NodeBudgetExceeded) as ex:
        print(c,K,type(ex).__name__,str(ex),'lifts',G.account['lifts'],'seconds',time.monotonic()-start,flush=True)
    finally: signal.alarm(0)
