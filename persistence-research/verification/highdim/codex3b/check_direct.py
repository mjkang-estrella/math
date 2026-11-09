"""Checkpointed subprocess launcher. Both checker source files run DIRECTLY under -I.
No imports from the checkers and no alteration of builtins or arithmetic.
"""
import sys
sys.dont_write_bytecode=True
import os,json,time,hashlib,subprocess,concurrent.futures,argparse,pathlib
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2]
def atomic(path,data):
 tmp=str(path)+'.tmp';open(tmp,'w').write(json.dumps(data,indent=1));os.replace(tmp,path)
def check(arg):
 path,kind,seconds,*extra=arg
 hd_workers=extra[0] if extra else 1
 rel=str(path.relative_to(HERE));meta=json.loads(open(path).readline());dim=meta['dim']
 brute={1:100,2:60,3:30,4:16}.get(dim,12)
 script=ROOT/('verification/highdim/codex/checkhd.py' if kind=='hd' else 'verification/v14_checknd_hd.py')
 log=HERE/'logs'/'checks'/kind/(path.stem+'.log');log.parent.mkdir(parents=True,exist_ok=True)
 # Each direct invocation independently receives the user's required VM limit.
 cmd=['bash','-c','ulimit -v 6000000; exec python3 -I -B "$@"','direct-check',str(script),str(path),str(brute)]+([str(hd_workers)] if kind=='hd' else [])
 start=time.monotonic()
 initial_sha=hashlib.sha256(path.read_bytes()).hexdigest()
 try:
  with open(log,'w') as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,timeout=seconds)
  content=log.read_text();status='PASS' if r.returncode==0 and 'RESULT: PASS' in content else 'FAIL'
  code=r.returncode
 except subprocess.TimeoutExpired:status='TIMEOUT';code=None
 if hashlib.sha256(path.read_bytes()).hexdigest()!=initial_sha:status='CHANGED_DURING_CHECK'
 return rel+'::'+kind,{'status':status,'returncode':code,'elapsed_s':round(time.monotonic()-start,3),'certificate_sha256':initial_sha,'checker':str(script.relative_to(ROOT)),'checker_sha256':hashlib.sha256(script.read_bytes()).hexdigest(),'brute_Lmax':brute,'command':cmd,'log':str(log.relative_to(HERE))}
def main():
 p=argparse.ArgumentParser();p.add_argument('--workers',type=int,default=12);p.add_argument('--seconds',type=int,default=1200);p.add_argument('--limit',type=int,default=999999);p.add_argument('--results',default='checker_results.json');p.add_argument('--glob',default='*.jsonl');p.add_argument("--kind",choices=("both","hd","v14"),default="both");p.add_argument("--hd-workers",type=int,default=1);a=p.parse_args();assert 1<=a.workers<=12
 fn=HERE/a.results;results=json.load(open(fn)) if fn.exists() else {}
 tasks=[]
 for path in sorted((HERE/'certs').rglob(a.glob)):
  sha=hashlib.sha256(path.read_bytes()).hexdigest()
  for kind in (('hd','v14') if a.kind=='both' else (a.kind,)):
   old=results.get(str(path.relative_to(HERE))+'::'+kind,{})
   if old.get('status')!='PASS' or old.get('certificate_sha256')!=sha:tasks.append((path,kind,a.seconds,a.hd_workers))
 tasks=tasks[:a.limit];print('TASKS',len(tasks),flush=True)
 with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool:
  for i,future in enumerate(concurrent.futures.as_completed([pool.submit(check,t) for t in tasks]),1):
   rec=future.result()
   key,result=rec;results[key]=result;atomic(fn,results);print(i,key,result['status'],result['elapsed_s'],flush=True)
 print('SUMMARY',{s:sum(x['status']==s for x in results.values()) for s in sorted({x['status'] for x in results.values()})},flush=True)
if __name__=='__main__':main()
