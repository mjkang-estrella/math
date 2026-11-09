from pathlib import Path
import subprocess,resource,time,json,os,hashlib
out=Path(__file__).parent
src=out/'frozen/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-jacobi-riccati-valuation-r4/formal/ArithmeticStart.lean'
lean='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
def limits():resource.setrlimit(resource.RLIMIT_AS,(16*1024**3,16*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(15,15))
cmd=[lean,'-j1','-M128',str(src)]
start=time.monotonic();peak=0;killed=False
with (out/'own-lean-attempt2.log').open('w') as log:
 p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,cwd=out,preexec_fn=limits,env={**os.environ,'MALLOC_ARENA_MAX':'2'})
 while p.poll() is None:
  try:
   for line in Path('/proc/'+str(p.pid)+'/status').read_text().splitlines():
    if line.startswith(('VmRSS:','VmHWM:')):peak=max(peak,int(line.split()[1]))
  except FileNotFoundError:pass
  if peak>450*1024 or time.monotonic()-start>20:p.kill();killed=True
  time.sleep(.01)
 rc=p.wait()
receipt=dict(command=cmd,returncode=rc,observed_rss_kib=peak,rss_guard_kib=450*1024,killed=killed,wall_seconds=time.monotonic()-start,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),scope='only five natural-number divisibility helpers; no literal source endpoint')
(out/'own-lean-attempt2-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));print((out/'own-lean-attempt2.log').read_text())
