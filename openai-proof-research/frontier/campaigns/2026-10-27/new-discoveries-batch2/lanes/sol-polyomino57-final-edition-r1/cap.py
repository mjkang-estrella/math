import os,sys,resource,subprocess,time,signal,json
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(210,)*2)
env=os.environ.copy()
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS','VECLIB_MAXIMUM_THREADS']: env[k]='1'
env['PYTHONDONTWRITEBYTECODE']='1'
env['XDG_CACHE_HOME']=os.path.abspath('cache')
p=subprocess.Popen(sys.argv[1:],env=env,start_new_session=True)
t=time.monotonic(); peak=0; reason=None
while p.poll() is None:
 rss=0
 for x in os.listdir('/proc'):
  if x.isdigit():
   try:
    s=open('/proc/'+x+'/stat').read().split()
    if int(s[4])==p.pid: rss+=int(s[23])*os.sysconf('SC_PAGE_SIZE')
   except (OSError,ValueError,IndexError): pass
 peak=max(peak,rss)
 if rss>512*1024**2 or time.monotonic()-t>230:
  reason='groupRSS' if rss>512*1024**2 else 'wall'; os.killpg(p.pid,signal.SIGKILL); break
 time.sleep(.045)
rc=p.wait()
with open('resource-receipts.jsonl','a') as f: f.write(json.dumps(dict(command=sys.argv[1:],exit=rc,wall=time.monotonic()-t,peak_group_rss=peak,limit_reason=reason,sampling_seconds=.045))+'\n')
sys.exit(rc if rc>=0 else 128-rc)
