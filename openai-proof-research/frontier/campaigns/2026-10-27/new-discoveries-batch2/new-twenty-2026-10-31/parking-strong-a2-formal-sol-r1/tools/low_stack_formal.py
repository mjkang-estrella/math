import os,sys,json,hashlib,resource,subprocess,shutil
from pathlib import Path
p=Path.cwd();pins=json.loads((p/'PINS.json').read_text())
resource.setrlimit(resource.RLIMIT_STACK,(1048576,1048576))
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for b in ['lean','leanchecker']:assert sha(Path(pins[b+'_bin']))==pins[b+'_sha256']
mode,module=sys.argv[1:];assert mode in ['compile','check']
source=p/'src'/(module+'.lean');out=p/'build'/(module+'.olean');before=sha(source)
env=dict(os.environ,PATH=str(Path(pins['lean_bin']).parent)+os.pathsep+os.environ.get('PATH',''),LEAN_PATH=os.pathsep.join([str(p/'build')]+pins['upstream_lean_paths']),LEAN_NUM_THREADS='1')
a=([pins['lean_bin'],'-j1','-s8192','-M3500','-DwarningAsError=true','-o',str(out),str(source)] if mode=='compile' else [pins['leanchecker_bin'],module])
if mode=='compile' and out.exists():
 archive=p/'cache'/(module+'.'+sha(out)+'.olean')
 if not archive.exists():shutil.copyfile(out,archive)
 out.unlink()
r=subprocess.run(a,env=env,capture_output=True,text=True)
print(r.stdout);print(r.stderr)
print(json.dumps(dict(mode=mode,module=module,argv=a,exit=r.returncode,source_sha256=before,olean_sha256=sha(out) if out.exists() else None,stack_rlimit_bytes=1048576,lean_stack_kib=8192)))
assert sha(source)==before
raise SystemExit(r.returncode)
