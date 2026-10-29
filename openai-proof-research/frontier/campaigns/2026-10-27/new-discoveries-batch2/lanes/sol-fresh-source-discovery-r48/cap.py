import os,sys,signal,subprocess,resource,time

def limits():
 resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
 resource.setrlimit(resource.RLIMIT_CPU,(210,210))
 os.setsid()
env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1',NUMEXPR_NUM_THREADS='1')
p=subprocess.Popen(sys.argv[1:],preexec_fn=limits,env=env)
start=time.monotonic(); reason=None
while p.poll() is None:
 cpu=0
 for d in os.scandir('/proc'):
  if not d.name.isdigit():continue
  try:
   s=open(d.path+'/stat').read().rsplit(')',1)[1].split()
   if int(s[2])==p.pid: cpu+=(int(s[11])+int(s[12]))/os.sysconf('SC_CLK_TCK')
  except (OSError,ValueError,IndexError):pass
 if time.monotonic()-start>230:reason='wall230s'
 if cpu>210:reason='groupCPU210s'
 if reason:
  os.killpg(p.pid,signal.SIGKILL);p.wait();print(reason,file=sys.stderr);sys.exit(124)
 time.sleep(.05)
sys.exit(p.returncode)
