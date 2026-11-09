import os,re,json,hashlib,subprocess,sys,shutil
from pathlib import Path
p=Path(__file__).resolve().parent
pins=json.loads((p/'PINS.json').read_text())
mode=os.environ['FORMAL_OPERATION'];module=os.environ['FORMAL_MODULE']
assert mode in ['compile','check'] and re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',module)
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(Path(pins['lean_bin']))==pins['lean_sha256'] and sha(Path(pins['leanchecker_bin']))==pins['leanchecker_sha256']
source=p/'src'/(module+'.lean');olean=p/'build'/(module+'.olean')
assert source.is_file();before=sha(source)
env=dict(os.environ);env['PATH']=str(Path(pins['lean_bin']).parent)+os.pathsep+env.get('PATH','');env['LEAN_PATH']=os.pathsep.join([str(p/'build')]+pins['upstream_lean_paths']);env['LEAN_NUM_THREADS']='1'
prior=sha(olean) if olean.exists() else None
if mode=='compile':
 if olean.exists():
  archive=p/'cache'/(module+'.'+prior+'.olean')
  if not archive.exists():shutil.copyfile(olean,archive)
  olean.unlink()
 args=[pins['lean_bin'],'-j1','-M3500','-DwarningAsError=true','-o',str(olean),str(source)]
else:
 assert olean.is_file(),'Kernel checker requires actual production olean'
 args=[pins['leanchecker_bin'],module]
r=subprocess.run(args,cwd=p,env=env,text=True,capture_output=True)
sys.stdout.write(r.stdout);sys.stderr.write(r.stderr)
after=sha(source);out=sha(olean) if olean.exists() else None
print(json.dumps(dict(stage=mode,module=module,argv=args,exit=r.returncode,source_sha256_before=before,source_sha256_after=after,olean_sha256_before=prior,olean_sha256_after=out,LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS=1)))
assert before==after,'Source changed during compile/check'
if r.returncode==0:
 assert out is not None,'No fresh olean produced'
 if mode=='check':assert prior==out,'Checker changed olean'
raise SystemExit(r.returncode)
