import os,resource,subprocess,sys,json,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);s=time.monotonic();peak=0
p=subprocess.Popen(sys.argv[1:])
while p.poll() is None:
 try:
  d=open(f'/proc/{p.pid}/status').read();rss=int(d.split('VmRSS:')[1].split()[0])*1024;peak=max(peak,rss)
 except (FileNotFoundError,IndexError):pass
 if peak>6*1024**3 or time.monotonic()-s>135:p.kill()
 time.sleep(.1)
print(json.dumps({'command':sys.argv[1:],'exit':p.returncode,'wall_seconds':time.monotonic()-s,'peak_sampled_rss_bytes':peak,'limits':'120 CPU,135 wall,2 CPUs,6GiB sampled RSS,64GiB AS'}),file=sys.stderr);sys.exit(p.returncode)
