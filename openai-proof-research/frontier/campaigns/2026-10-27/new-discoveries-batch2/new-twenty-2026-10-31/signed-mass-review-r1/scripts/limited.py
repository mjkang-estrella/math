import os,resource,sys,subprocess,time
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
p=subprocess.Popen(sys.argv[1:]);start=time.monotonic();peak=0
while p.poll() is None:
 try:
  st=open(f'/proc/{p.pid}/status').read();rss=int(st.split('VmRSS:')[1].split()[0]);peak=max(peak,rss)
  if rss>6*1024**2 or time.monotonic()-start>139:p.kill()
 except (FileNotFoundError,IndexError):pass
 time.sleep(.1)
print(f'LIMIT RECEIPT: exit={p.returncode} peak_rss_kib={peak} wall_seconds={time.monotonic()-start:.3f}',file=sys.stderr)
sys.exit(p.returncode)
