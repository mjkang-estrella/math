from pathlib import Path
import subprocess,os,resource,time,json,sys,signal
p=Path(__file__).resolve().parent
def limit():
 resource.setrlimit(resource.RLIMIT_CPU,(110,110))
env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1',LEAN_NUM_THREADS='1')
f=sys.argv[1]
t=time.monotonic()
logs=p/'logs';logs.mkdir(exist_ok=True)
with (logs/(f+'.log')).open('w') as log:
 proc=subprocess.Popen(['python3','run_lean.py','-j1','-DwarningAsError=true','-DautoImplicit=false',f,'-o',f.replace('.lean','.olean')],cwd=p/'formal',env=env,preexec_fn=limit,start_new_session=True,stdout=log,stderr=log)
 peak=0;failure=None
 while proc.poll() is None:
  ids=[proc.pid]
  for pid in ids:
   try:ids.extend(map(int,Path(f'/proc/{pid}/task/{pid}/children').read_text().split()))
   except FileNotFoundError:pass
  rss=0
  for pid in ids:
   try:
    for line in Path(f'/proc/{pid}/status').read_text().splitlines():
     if line.startswith('VmRSS:'):rss+=int(line.split()[1])
   except FileNotFoundError:pass
  peak=max(peak,rss)
  if rss>=3*1024**2:failure='RSS ceiling'
  if time.monotonic()-t>120:failure='wall timeout'
  if failure:os.killpg(proc.pid,signal.SIGKILL);proc.wait();break
  time.sleep(.02)
record=dict(file=f,exit=proc.returncode,wall=time.monotonic()-t,sampledPeakRSS_KiB=peak,failure=failure,command=['python3','run_lean.py','-j1','-DwarningAsError=true','-DautoImplicit=false',f,'-o',f.replace('.lean','.olean')])
(logs/(f+'.json')).write_text(json.dumps(record,indent=2)+'\n')
print((logs/(f+'.log')).read_text());print(json.dumps(record))
sys.exit(1 if failure else proc.returncode)
