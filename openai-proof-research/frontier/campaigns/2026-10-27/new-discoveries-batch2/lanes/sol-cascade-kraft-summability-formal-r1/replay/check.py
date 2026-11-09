import os,sys,subprocess,time,json,signal
from pathlib import Path
b=Path(__file__).resolve().parent; f=b/'formal'; logs=b/'verification'; logs.mkdir(exist_ok=True)
rs=[]
for name in sys.argv[1:]:
 cmd=['python','run_lean.py','-DautoImplicit=false','-DwarningAsError=true','-o',name+'.olean',name+'.lean']
 out=logs/(name+'-'+str(time.time_ns())+'.log');start=time.monotonic();peak=0;reason=None
 with out.open('w') as o:
  p=subprocess.Popen(cmd,cwd=f,stdout=o,stderr=subprocess.STDOUT,start_new_session=True,env={**os.environ,**{k:'1' for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']}})
  while p.poll() is None:
   rss=0
   for d in Path('/proc').iterdir():
    if d.name.isdigit():
     try:
      st=(d/'stat').read_text().split()
      if int(st[4])==p.pid:
       status=(d/'status').read_text();rss+=int(status.split('VmRSS:')[1].split()[0])*1024
     except (OSError,ValueError,IndexError):pass
   peak=max(peak,rss)
   if peak>=3*1024**3 or time.monotonic()-start>120:
    reason='RSS' if peak>=3*1024**3 else 'wall';os.killpg(p.pid,signal.SIGKILL);p.wait();break
   time.sleep(.1)
 r=dict(module=name,cmd=cmd,cwd=str(f),log=str(out),exit=p.returncode,seconds=time.monotonic()-start,process_group_peak_RSS=peak,kill_reason=reason);rs.append(r);print(json.dumps(r),flush=True);print(out.read_text(),flush=True)
 if p.returncode:break
(logs/('receipt-'+str(time.time_ns())+'.json')).write_text(json.dumps(rs,indent=2))
