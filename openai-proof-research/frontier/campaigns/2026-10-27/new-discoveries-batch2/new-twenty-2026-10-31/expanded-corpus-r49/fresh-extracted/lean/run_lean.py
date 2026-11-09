# Managed Lean check: 2 CPUs, 64 GiB virtual address cap (resident memory capped by systemd scope MemoryMax=8G), CPU-time cap; explicit read-only mathlib oleans.
import pathlib,os,resource,subprocess,sys
O=pathlib.Path(__file__).resolve().parent
cpu=int(os.environ.get('LEAN_CPU','1500'))
resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,)*2); resource.setrlimit(resource.RLIMIT_CPU,(cpu,cpu))
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
root=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
paths=[root/'.lake/packages'/x/'.lake/build/lib/lean' for x in ['mathlib','batteries','Qq','aesop','proofwidgets','LeanSearchClient','importGraph','plausible','Cli']]
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[O]+paths));env['LEAN_NUM_THREADS']='2'
r=subprocess.run(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','-j2','-DwarningAsError=true',*sys.argv[1:]],cwd=O,env=env,timeout=cpu+60);sys.exit(r.returncode)
