"""Bounded heterogeneous first-slice schedule probes, checkpoint each attempt."""
import sys
sys.dont_write_bytecode=True
import os,json,multiprocessing as mp,importlib.util,collections
HERE=os.path.dirname(os.path.abspath(__file__));sys.path.insert(0,HERE)
spec=importlib.util.spec_from_file_location('continuation',os.path.join(HERE,'continue.py'));C=importlib.util.module_from_spec(spec);sys.modules['continuation']=C;spec.loader.exec_module(C)
if __name__=='__main__':
 stage=sys.argv[1];cap=float(sys.argv[2]) if len(sys.argv)>2 else 90
 bas=C.BASE
 small=sorted([k for k,v in bas.items() if len(v['far'])==3])
 keys=small+sorted([k for k,v in bas.items() if len(v['far'])==4 and v['certs']==1])[:8]
 jobs=[]
 for name in ('old','rich2','ord22'):
  for k in keys:
   if name=='ord22' and k not in small:continue
   jobs.append((k,stage+'_'+name,cap,2000000,100000000,name,10**24,120,True,True))
 fn=os.path.join(HERE,'experiments_'+stage+'.json');results=json.load(open(fn)) if os.path.exists(fn) else {}
 jobs=[j for j in jobs if j[0]+'::'+j[5] not in results]
 print('START',len(jobs),flush=True)
 with mp.get_context('fork').Pool(11,maxtasksperchild=1) as pool:
  for k,r in pool.imap_unordered(C.work,jobs,chunksize=1):
   results[k+'::'+r['schedule_name']]=r;C.breadth.atomic_json(fn,results)
   print(k,r['schedule_name'],r['status'],r['elapsed_s'],r['stop_reason'],flush=True)
 print('SUMMARY',collections.Counter(r['status'] for r in results.values()),flush=True)
