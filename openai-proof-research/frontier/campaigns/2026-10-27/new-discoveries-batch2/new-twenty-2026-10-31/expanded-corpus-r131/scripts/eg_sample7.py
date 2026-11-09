import sys, random, time, json, importlib.util, pathlib
D=pathlib.Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('egf',D/'eg_fast.py'); egf=importlib.util.module_from_spec(s); s.loader.exec_module(egf)
s2=importlib.util.spec_from_file_location('eg',D/'eg.py'); eg=importlib.util.module_from_spec(s2); s2.loader.exec_module(eg)
n=int(sys.argv[1]); seed=int(sys.argv[2]); out=sys.argv[3]; N=n*(n-1)//2
rng=random.Random(seed); t0=time.time(); done=0; bad=[]; mx=0
import resource
resource.setrlimit(resource.RLIMIT_AS,(1536*1024**2,1536*1024**2))
while time.time()-t0<100:
    if len(egf._ins)>200000: egf._ins.clear()
    Q=tuple(tuple(r) for r in eg.random_syt(n,rng)); r=egf.check(Q,N,n); done+=1; mx=max(mx,r.get('size',0))
    if r.get('error') or not r['maximal'] or not r['unitchain']: bad.append((Q,r)); print('FAIL',Q,r,flush=True)
rec=dict(n=n,seed=seed,sampled_uniform_hook_walk=done,max_WQ=mx,failures=bad,seconds=time.time()-t0)
json.dump(rec,open(out,'w')); print(json.dumps(rec)[:400])
