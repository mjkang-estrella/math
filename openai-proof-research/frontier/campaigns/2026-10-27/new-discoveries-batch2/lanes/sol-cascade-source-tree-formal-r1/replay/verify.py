import subprocess,os,time,json,hashlib
from pathlib import Path
base=Path(__file__).resolve().parent
os.chdir(base/'formal')
logs=base/'verification';logs.mkdir(exist_ok=True)
receipts=[]
for name in ['DepthDefs','SourceDefs','TreeConstruction','Audit']:
 if not Path(name+'.lean').exists():continue
 cmd=['python','run_lean.py','-DautoImplicit=false','-DwarningAsError=true','-o',name+'.olean',name+'.lean']
 start=time.monotonic(); peak=0
 with (logs/(name+'.log')).open('w') as out:
  p=subprocess.Popen(cmd,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
  while p.poll() is None:
   # runner plus its Lean child, read /proc without diagnostics allocations
   for d in Path('/proc').iterdir():
    if d.name.isdigit():
     try:
      stat=(d/'stat').read_text().split()
      if int(stat[5])==p.pid:
       status=(d/'status').read_text()
       rss=int(status.split('VmRSS:')[1].split()[0])*1024
       peak=max(peak,rss)
     except (OSError,ValueError,IndexError):pass
   if peak>=3*1024**3 or time.monotonic()-start>120:
    import signal
    os.killpg(p.pid,signal.SIGKILL);p.wait();break
   time.sleep(.15)
 r=dict(module=name,command=cmd,exit=p.returncode,seconds=time.monotonic()-start,peakRSS=peak)
 receipts.append(r)
 print(r,flush=True)
 if p.returncode:break
(logs/'receipt.json').write_text(json.dumps(receipts,indent=2)+'\n')
