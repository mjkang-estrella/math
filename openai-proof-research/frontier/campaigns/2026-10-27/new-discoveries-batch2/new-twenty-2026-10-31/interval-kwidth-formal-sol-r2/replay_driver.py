import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));
from pathlib import Path
import subprocess,json,os,resource,hashlib
p=json.loads(Path('PINS.json').read_text());mods=json.loads(Path('results/336276.json').read_text())['strict_green_modules'];root=Path.cwd();b=root/'replay2/build';b.mkdir(parents=True,exist_ok=False)
w=str(root/'write_lane.py')
def put(f,s):
 r=subprocess.run(['python3','-I','-B',w,f],input=s,text=True,capture_output=True);assert r.returncode==0
for key in ['lean','leanchecker']:assert hashlib.sha256(Path(p[key+'_bin']).read_bytes()).hexdigest()==p[key+'_sha256']
resource.setrlimit(resource.RLIMIT_STACK,(512*1024,512*1024));env=dict(os.environ,PATH=str(Path(p['lean_bin']).parent)+os.pathsep+os.environ.get('PATH',''),LEAN_PATH=os.pathsep.join([str(b)]+p['upstream_lean_paths']),LEAN_NUM_THREADS='1');out=[]
for m in mods:
 data=(root/'src'/(m+'.lean')).read_text();put('replay2/src/'+m+'.lean',data);s=root/'replay2/src'/(m+'.lean');o=b/(m+'.olean');sh=hashlib.sha256(s.read_bytes()).hexdigest()
 args=[p['lean_bin'],'-j1','-s8192','-M3500','-DwarningAsError=true','-o',str(o),str(s)]
 r=subprocess.run(args,cwd=root/'replay2',env=env,text=True,capture_output=True);put('replay2/logs/'+m+'.compile.log',r.stdout+r.stderr);record=dict(module=m,compile_exit=r.returncode,source_sha256=sh,compile_argv=args)
 if r.returncode==0:
  c=subprocess.run([p['leanchecker_bin'],m],cwd=root/'replay2',env=env,text=True,capture_output=True);put('replay2/logs/'+m+'.kernel.log',c.stdout+c.stderr);record['kernel_exit']=c.returncode;record['olean_sha256']=hashlib.sha256(o.read_bytes()).hexdigest()
 assert hashlib.sha256(s.read_bytes()).hexdigest()==sh and s.read_bytes()==(root/'src'/(m+'.lean')).read_bytes()
 out.append(record);put('replay2/results.json',json.dumps(out,indent=2));print(m,record['compile_exit'],record.get('kernel_exit'))
 if record.get('kernel_exit')!=0:raise SystemExit(1)
print('SOURCE_ONLY_EMPTY_BUILD_REPLAY_PASSED',len(out))
