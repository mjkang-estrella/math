import subprocess,os,time,json,hashlib,sys,shutil
from pathlib import Path
base=Path(__file__).resolve().parent
os.chdir(base/'formal')
logs=base/'verification';logs.mkdir(exist_ok=True)
receipts=[]
for name in (sys.argv[1:] or ['DepthDefs','SourceDefs','TreeConstruction','DepthArithmetic','DepthAnalysis','SelectedFamily','SelectedCounting','Audit']):
 if not Path(name+'.lean').exists():continue
 cmd=['python','run_lean.py','-DautoImplicit=false','-DwarningAsError=true','-o',name+'.olean',name+'.lean']
 start=time.monotonic(); peak=0
 if (logs/(name+'.log')).exists():
  shutil.copyfile(logs/(name+'.log'),logs/(name+'.'+str(time.time_ns())+'.log'))
 with (logs/(name+'.log')).open('w') as out:
  p=subprocess.Popen(cmd,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
  while p.poll() is None:
   # runner plus its Lean child, read /proc without diagnostics allocations
   sampleRSS=0
   for d in Path('/proc').iterdir():
    if d.name.isdigit():
     try:
      stat=(d/'stat').read_text().split()
      if int(stat[5])==p.pid:
       status=(d/'status').read_text()
       rss=int(status.split('VmRSS:')[1].split()[0])*1024
       sampleRSS+=rss
     except (OSError,ValueError,IndexError):pass
   peak=max(peak,sampleRSS)
   if peak>=3*1024**3 or time.monotonic()-start>180:
    import signal
    os.killpg(p.pid,signal.SIGKILL);p.wait();break
   time.sleep(.15)
 r=dict(module=name,command=cmd,cwd=str(Path.cwd()),source_sha256=hashlib.sha256(Path(name+'.lean').read_bytes()).hexdigest(),wall_limit_seconds=180,sampled_group_rss_limit_bytes=3*1024**3,sample_interval_seconds=.15,exit=p.returncode,seconds=time.monotonic()-start,peakRSS=peak)
 receipts.append(r)
 print(r,flush=True)
 if p.returncode:break
(logs/'receipt.json').write_text(json.dumps(receipts,indent=2)+'\n')

raise SystemExit(0 if receipts and all(r["exit"]==0 for r in receipts) else 1)
