from pathlib import Path
import hashlib,json,zipfile,subprocess,os,resource,time,datetime,urllib.request,sys
D=Path(__file__).resolve().parents[1]; S=D.parent/'expanded-corpus-r83'; root=Path('/home/mj-kang/Documents/Dev/math'); F=D/os.environ.get('PROOF_BUILD_DIR','formal'); B=root/'dlp-research/.tools/lean-4.34.1-linux/bin'; P=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def limits():
 os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2])); resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
def run(name,args):
 env={'XDG_RUNTIME_DIR':'/run/user/1000','DBUS_SESSION_BUS_ADDRESS':'unix:path=/run/user/1000/bus','PATH':str(B)+':/usr/bin:/bin','LANG':'C.UTF-8','LEAN_PATH':str(F)+':'+':'.join(str(p) for p in sorted(P.glob('*/.lake/build/lib/lean'))),'LEAN_NUM_THREADS':'1','MALLOC_ARENA_MAX':'2'}
 t=time.monotonic()
 with (D/'logs'/(name+'.log')).open('w') as log:
  p=subprocess.Popen(["systemd-run","--user","--scope","--quiet","-p","MemoryMax=6G",*args],cwd=F,env=env,preexec_fn=limits,stdout=log,stderr=subprocess.STDOUT)
  peak=0
  def private(pid):
   total=0
   try:
    for line in Path(f'/proc/{pid}/smaps_rollup').read_text().splitlines():
     if line.startswith(('Private_Clean:', 'Private_Dirty:', 'Private_Hugetlb:')):total+=int(line.split()[1])*1024
    for ch in Path(f'/proc/{pid}/task/{pid}/children').read_text().split():total+=private(int(ch))
   except (OSError,ValueError):pass
   return total
  while p.poll() is None:
   peak=max(peak,private(p.pid))
   if time.monotonic()-t>140 or peak>6*1024**3:
    p.kill();p.wait();break
   time.sleep(.1)
  rc=p.returncode
 r={'peak_sampled_private_rss_bytes':peak,'memory_cgroup_limit_bytes':6*1024**3,'cpu_limit_seconds':120,'affinity_cpus':sorted(os.sched_getaffinity(0))[:2],'wall_limit_seconds':140,'command':args,'rc':rc,'seconds':time.monotonic()-t,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'log_sha256':sha(D/'logs'/(name+'.log'))};(D/'logs'/(name+'.json')).write_text(json.dumps(r,indent=2));print(r)
 return r

if __name__=="__main__":
 name=sys.argv[1]; args=sys.argv[2:]; run(name,args)
