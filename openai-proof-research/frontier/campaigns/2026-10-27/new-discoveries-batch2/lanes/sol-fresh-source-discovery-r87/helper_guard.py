import os,sys,time,resource,subprocess,signal,json
LIMIT=512*1024*1024
resource.setrlimit(resource.RLIMIT_AS,(LIMIT,resource.RLIM_INFINITY))
resource.setrlimit(resource.RLIMIT_CPU,(210,210))
os.environ.update({k:'1' for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS','BLIS_NUM_THREADS']})
def pre():
 resource.setrlimit(resource.RLIMIT_AS,(LIMIT,resource.RLIM_INFINITY));resource.setrlimit(resource.RLIMIT_CPU,(210,210))
p=subprocess.Popen(sys.argv[1:],start_new_session=True,preexec_fn=pre)
def stop(signum,frame):
 try: os.killpg(p.pid,signal.SIGKILL)
 except ProcessLookupError: pass
 p.wait()
 raise SystemExit(128+signum)
for sig in (signal.SIGTERM,signal.SIGINT,signal.SIGALRM):signal.signal(sig,stop)
signal.alarm(230)
start=time.monotonic();peak=0;reason=None;hz=os.sysconf('SC_CLK_TCK')
while p.poll() is None:
 sample_start=time.monotonic()
 rss=cpu=0
 for name in os.listdir('/proc'):
  if not name.isdigit():continue
  try:
   data=open('/proc/'+name+'/stat').read().rsplit(')',1)[1].split()
   if int(data[2])!=p.pid:continue
   rss+=int(data[21])*os.sysconf('SC_PAGE_SIZE');cpu+=(int(data[11])+int(data[12]))/hz
  except (FileNotFoundError,ProcessLookupError,PermissionError):pass
 peak=max(peak,rss)
 if rss>LIMIT:reason='process-group RSS >512MiB'
 if cpu>210:reason='process-group sampled CPU >210s'
 if time.monotonic()-start>230:reason='wall >230s'
 if reason:
  os.killpg(p.pid,signal.SIGKILL);break
 time.sleep(max(0,.04-(time.monotonic()-sample_start)))
code=p.wait();print(json.dumps({'guard_exit':code,'reason':reason,'sampled_peak_group_rss':peak,'wall_seconds':time.monotonic()-start}),file=sys.stderr)
sys.exit(code if code>=0 else 128-code)
