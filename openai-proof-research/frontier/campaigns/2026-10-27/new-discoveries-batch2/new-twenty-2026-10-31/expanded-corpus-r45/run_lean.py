import pathlib,os,resource
O=pathlib.Path(__file__).resolve().parent
resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3))
resource.setrlimit(resource.RLIMIT_CPU,(100,100))
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
import subprocess,sys
root=O.parents[5]/'2026-10-14/formal'
root=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
paths=[root/'.lake/packages'/x/'.lake/build/lib/lean' for x in ['mathlib','batteries','Qq','aesop','proofwidgets','LeanSearchClient','importGraph','plausible','Cli']]
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[O]+paths));env['LEAN_NUM_THREADS']='2'
r=subprocess.run(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','-j2','-DwarningAsError=true',*sys.argv[1:]],cwd=O,env=env,timeout=95);sys.exit(r.returncode)
