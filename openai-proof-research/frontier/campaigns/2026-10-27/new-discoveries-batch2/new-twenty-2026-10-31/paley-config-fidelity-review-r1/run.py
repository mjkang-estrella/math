import os,pathlib,subprocess,resource,json,time,hashlib,sys
D=pathlib.Path(__file__).resolve().parent; L=D/'extracted/lean'; B=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin'); P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env={'HOME':os.environ['HOME'],'PATH':str(B)+':/usr/bin:/bin','LEAN_PATH':':'.join(map(str,[L]+[P/x/'.lake/build/lib/lean' for x in ['mathlib','batteries','Qq','aesop','proofwidgets','LeanSearchClient','importGraph','plausible','Cli']])),'LEAN_NUM_THREADS':'1','MALLOC_ARENA_MAX':'2'}
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,)*2);resource.setrlimit(resource.RLIMIT_CPU,(120,)*2);os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
def run(name,args):
 t=time.monotonic()
 with (D/(name+'.log')).open('w') as f:
  p=subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryMax=6G','-p','CPUQuota=200%','timeout','140',*args],cwd=L,env={**{k:os.environ[k] for k in ["XDG_RUNTIME_DIR","DBUS_SESSION_BUS_ADDRESS","LANG"] if k in os.environ},**env},stdout=f,stderr=subprocess.STDOUT,preexec_fn=limits)
 r={'name':name,'returncode':p.returncode,'seconds':time.monotonic()-t,'args':args};print(r,flush=True);return r
if __name__=='__main__':
 out=[]
 for m in ['Yip355956','V3Config355701']:
  out.append(run('build-'+m,[str(B/'lean'),'-j1','-DwarningAsError=true','-o',m+'.olean',m+'.lean']))
 (D/'builds.json').write_text(json.dumps(out,indent=2))
