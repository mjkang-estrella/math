import subprocess,sys,time,pathlib
p=subprocess.Popen(sys.argv[1:])
while p.poll() is None:
 try:
  s=pathlib.Path('/proc',str(p.pid),'status').read_text()
  rss=int(s.split('VmRSS:')[1].split()[0]) if 'VmRSS:' in s else 0
  if rss>6*1024*1024:
   print('RSS CAP EXCEEDED: terminating',p.pid,rss,flush=True);p.kill()
 except FileNotFoundError:pass
 time.sleep(.05)
sys.exit(p.returncode)
