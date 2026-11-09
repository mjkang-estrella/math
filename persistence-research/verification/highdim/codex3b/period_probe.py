"""Search-only comparison of an alternate period-17 schedule; emits NO certificates."""
import sys
sys.dont_write_bytecode=True
import pathlib,json,time,signal,multiprocessing as mp,os,collections
HERE=pathlib.Path(__file__).resolve().parent;sys.path.insert(0,str(HERE))
import breadth,gen_hd
from optimize import FastGen
class BG(breadth.BudgetGen,FastGen):
 def test(self,e,r,a,w):
  ans=super().test(e,r,a,w)
  if e[0] in self.new_ps:
   self.new_trials[e[0]]+=1
   if ans:self.new_kills[e[0]]+=1
  return ans
SCHED=[2,17,3,2,3,2,2,3,5,7]
def work(arg):
 name,K,coefs,source=arg;start=time.monotonic();seconds=60
 supply=json.load(open(HERE/source));old={v[0] for v in json.load(open(HERE/'supply_B.json'))}
 G=BG(coefs,K,3,supply,False,maxp=10**12);G.account={'lifts':0,'max_lifts':100000000};G.candidate_factors=(2,3,5)
 G.new_ps={v[0] for v in supply}-old;G.new_trials=collections.Counter();G.new_kills=collections.Counter()
 log=open(HERE/('period17_'+name+'_'+source.replace('.json','')+'.log'),'w',buffering=1);sys.stderr=log
 def alarm(s,f):raise breadth.Budget('wall time')
 signal.signal(signal.SIGALRM,alarm);signal.setitimer(signal.ITIMER_REAL,seconds)
 ns=None;info=[];status=None;used=set()
 try:ns,info,status=gen_hd.run(G,SCHED,workers=1,cap_level=2000000,max_nodes=2000000,budget_s=seconds,mcap=10**24,maxdepthB=120)
 except (breadth.Budget,gen_hd.NodeBudgetExceeded,MemoryError) as e:status=str(e)
 finally:
  try:signal.setitimer(signal.ITIMER_REAL,0)
  except breadth.Budget:status='wall time in teardown';signal.setitimer(signal.ITIMER_REAL,0)
 if ns is not None:
  for n in ns.values():
   used.update(n.get('rest',[]))
   if n.get('k')=='l' and 'prime' in n['x']:used.add(n['x']['prime'])
 log.close()
 return name+'::'+source,{'label':'COMPUTED search only; no certificate emitted and no new proof claim','K':K,'coefs':coefs,'supply':source,'schedule':SCHED,'status':status,'complete_tree':ns is not None,'nodes':len(ns) if ns else None,'frontiers':info,'lifts_attempted':G.account['lifts'],'elapsed_s':time.monotonic()-start,'new_supply_primes_used_in_complete_tree':sorted(used-old),'new_prime_test_counts':dict(G.new_trials),'new_prime_kill_counts':dict(G.new_kills),'diagnostic':getattr(G,'diagnostic',None)}
if __name__=='__main__':
 args=[(n,K,c,s) for n,K,c in [('S37',332,[54,54,72]),('S676',6083,[9,18,45])] for s in ('supply_B.json','supply_extended.json')]
 result={}
 with mp.get_context('fork').Pool(2,maxtasksperchild=1) as pool:
  for k,r in pool.imap_unordered(work,args,chunksize=1):
   result[k]=r;breadth.atomic_json(str(HERE/'period17_results.json'),result);print(k,r['status'],r['complete_tree'],r['elapsed_s'],flush=True)
