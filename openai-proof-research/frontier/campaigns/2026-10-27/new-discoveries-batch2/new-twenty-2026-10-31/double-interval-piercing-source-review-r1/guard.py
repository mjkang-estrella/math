import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,subprocess,time,json,hashlib,pathlib
lane=pathlib.Path(__file__).resolve().parent
label=sys.argv[1]; source=sys.stdin.read(); started=time.time(); samples=[]
def run(args,data):
 p=subprocess.Popen(args,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
 p.stdin.write(data);p.stdin.close(); p.stdin=None
 peak={}; seen=set()
 while p.poll() is None:
  todo=[p.pid]; total=0
  while todo:
   pid=todo.pop()
   try:
    status=pathlib.Path('/proc/'+str(pid)+'/status').read_text(); rss=int(next((x.split()[1] for x in status.splitlines() if x.startswith('VmRSS:')),'0'));total+=rss;peak[pid]=max(peak.get(pid,0),rss);seen.add(pid)
    todo+=list(map(int,pathlib.Path('/proc/'+str(pid)+'/task/'+str(pid)+'/children').read_text().split()))
   except (FileNotFoundError,ProcessLookupError):pass
  samples.append(total)
  if total>6*1024**2 or time.time()-started>130:p.kill()
  time.sleep(.01)
 out,err=p.communicate();return {'argv':args,'exit':p.returncode,'pids_observed':sorted(seen),'peak_by_pid_KiB':peak,'stdout':out,'stderr':err}
r=run([sys.executable,'-I','-B','-c',source],'');print(r['stdout'],end='');print(r['stderr'],end='',file=sys.stderr)
receipt={'label':label,'utc_start':started,'utc_end':time.time(),'affinity':sorted(os.sched_getaffinity(0)),'CPU':resource.getrlimit(resource.RLIMIT_CPU),'AS':resource.getrlimit(resource.RLIMIT_AS),'sample_interval_s':.01,'sampled_not_cgroup':True,'worker':r,'guard_self_peak_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
w=run([sys.executable,'-I','-B',str(lane/'write_lane.py'),'receipts/'+label+'.json'],json.dumps(receipt,indent=2)+'\n');print('RECEIPT_WRITER',json.dumps(w));print('GUARD_EXIT',r['exit']);sys.exit(r['exit'])
