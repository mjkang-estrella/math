import pathlib,os,resource,subprocess,time,json,hashlib
p=pathlib.Path(__file__).resolve().parent
pk=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
binary='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
os.sched_setaffinity(0,{0,1})
resource.setrlimit(resource.RLIMIT_CPU,(60,60))
resource.setrlimit(resource.RLIMIT_AS,(16*1024**3,16*1024**3))
s=(p/'Attempt.lean').read_text().split('-- Direct literal finite-set endpoint attempt;')[0]
names=['Subset15','family','core','fano','sourceFamily','Bicommutative','instDecidableBicommutative']
s+='\n'+'\n'.join('#print axioms '+n for n in names)+'\nend Bicommutative338640\n'
fresh=p/'fresh-definitions';fresh.mkdir(exist_ok=True)
(fresh/'Definitions.lean').write_text(s)
env={'PATH':'/usr/bin:/bin','HOME':str(fresh),'LANG':'C.UTF-8','LEAN_PATH':':'.join(str(x/'.lake/build/lib/lean') for x in pk.iterdir())}
cmd=[binary,'-j1','-M2048','-DwarningAsError=true',str(fresh/'Definitions.lean')]
t=time.monotonic()
try:
 r=subprocess.run(cmd,env=env,cwd=fresh,capture_output=True,text=True,timeout=65);code=r.returncode;log=r.stdout+r.stderr
except subprocess.TimeoutExpired as e:
 code='timeout';log=str(e)
(p/'definitions.log').write_text(log)
receipt={'scope':'definitions-only; no counterexample theorem or completed endpoint','returncode':code,'command':cmd,'sanitized_env':env,'wall_seconds':time.monotonic()-t,'cpu_cap_seconds':60,'wall_cap_seconds':65,'address_space_cap_GiB':16,'Lean_managed_memory_MiB':2048,'affinity':[0,1],'maxrss_children_KiB':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'Lean_version':'4.34.1','mathlib_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612','source_sha256':hashlib.sha256(s.encode()).hexdigest(),'audited_names':names,'trust':'Existing pinned upstream prebuilt oleans trusted, not rebuilt'}
(p/'definitions-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));print(log)
