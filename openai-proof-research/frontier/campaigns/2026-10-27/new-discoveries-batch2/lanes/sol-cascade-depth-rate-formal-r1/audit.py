import pathlib,subprocess,os,time,json,hashlib,sys
base=pathlib.Path(__file__).resolve().parent
root=base.parent/'root-cascade-formal-r1'
files=[root/'formal/DepthDefs.lean',root/'formal/run_lean.py',root/'ADOPTION.md',root/'definition-freeze.json']
def hashes(): return {str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
if sys.argv[1]=='freeze':
 (base/'frozen-before.json').write_text(json.dumps(hashes(),indent=2));sys.exit()
wd=base/sys.argv[1]; args=sys.argv[2:];log=base/(('deps-' if '--deps' in args else '')+sys.argv[1].replace('/','_')+'-'+pathlib.Path(args[-1]).stem+'.log')
env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1',NUMEXPR_NUM_THREADS='1')
start=time.monotonic(); peak=0
with log.open('w') as out:
 p=subprocess.Popen([sys.executable,str(wd/'run_lean.py'),*args],cwd=wd,stdout=out,stderr=subprocess.STDOUT,env=env,start_new_session=True)
 while p.poll() is None:
  # sample every process in this isolated process group
  for d in pathlib.Path('/proc').iterdir():
   if not d.name.isdigit():continue
   try:
    if os.getpgid(int(d.name))==p.pid:
     for line in (d/'status').read_text().splitlines():
      if line.startswith('VmRSS:'):peak=max(peak,int(line.split()[1])*1024)
   except (ProcessLookupError,FileNotFoundError,PermissionError):pass
  if peak>=3*1024**3 or time.monotonic()-start>180:
   import signal;os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.1)
 code=p.wait()
receipt={'args':args,'cwd':str(wd),'exit':code,'wall':time.monotonic()-start,'sampled_peakRSS':peak,'frozen':hashes()}
(base/(log.stem+'.json')).write_text(json.dumps(receipt,indent=2))
print(json.dumps(receipt));print(log.read_text());sys.exit(code)
