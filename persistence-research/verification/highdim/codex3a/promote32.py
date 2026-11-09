import sys
sys.dont_write_bytecode=True
import os,pickle,json
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
C=__import__('continue');HERE=C.HERE
profile=sys.argv[1];data=pickle.load(open(os.path.join(HERE,f'opt32_{profile}.pickle'),'rb'))
G=C.FastGen([9]*4,89,3,C.run_target.SUP,False,maxp=10**12)
job=C.breadth.jobs_for(32,10,[9]*4)[0];fn=job[-1]
C.gen_hd.write_cert(fn+'.tmp',G,data['nodes'],{'sched':data['schedule'],'maxp':10**12,'search_profile':profile,
    'certificate_lifts':data['stats']['certificate_lifts']})
os.replace(fn+'.tmp',fn)
incoming=json.load(open(os.path.join(HERE,'incoming_t32.json')))['10|9,9,9,9']
r={'multiset':incoming['multiset'],'S_low':10,'far':[9]*4,'status':'CLOSED','slices':1,'certs':1,
   'jobs':[{'K':89,'coefs':[9]*4,'qmin':3,'domain':'unordered','file':os.path.relpath(fn,HERE),
      'status':'closed','info':data['stats']}],'pending_jobs':0,'sz_solutions':C.gen_hd.solutions(data['nodes']),
   'budget':{'seconds':300,'nodes':2000000,'lifts':500000000,'profile':profile,'mcap':10**12},
   'elapsed_s':data['stats']['seconds'],'lifts_attempted':data['stats']['lifts'],'stop_reason':None}
with open(os.path.join(HERE,'history.jsonl'),'a') as f:f.write(json.dumps({'target':32,'key':'10|9,9,9,9','result':r})+'\n')
res=json.load(open(os.path.join(HERE,'results_t32.json')));res['10|9,9,9,9']=r
C.breadth.atomic_json(os.path.join(HERE,'results_t32.json'),res)
print('PROMOTED',profile,data['stats'])
