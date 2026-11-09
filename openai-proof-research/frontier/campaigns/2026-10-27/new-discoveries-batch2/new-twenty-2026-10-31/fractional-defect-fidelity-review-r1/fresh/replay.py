from pathlib import Path
import os,resource,subprocess,json,time,hashlib
root=Path(__file__).resolve().parent
pk=Path(os.environ.get('MATHLIB_PACKAGES','/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'))
lean=os.environ.get('LEAN_BINARY','/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
env=dict(os.environ,LEAN_PATH=':'.join(str(p/'.lake/build/lib/lean') for p in pk.iterdir() if (p/'.lake/build/lib/lean').exists()))
def limit():
 resource.setrlimit(resource.RLIMIT_CPU,(90,95))
 resource.setrlimit(resource.RLIMIT_AS,(8*1024**3,8*1024**3))
cmd=[lean,'-DwarningAsError=true','-j','1','-M','2048','-o',str(root/'FractionalDefect.olean'),str(root/'FractionalDefect.lean')]
t=time.monotonic();p=subprocess.run(cmd,cwd=root,env=env,capture_output=True,text=True,timeout=105,preexec_fn=limit);log=p.stdout+p.stderr;(root/'replay.log').write_text(log)
r=dict(command=cmd,exit_code=p.returncode,seconds=time.monotonic()-t,source_sha256=hashlib.sha256((root/'FractionalDefect.lean').read_bytes()).hexdigest(),log_sha256=hashlib.sha256(log.encode()).hexdigest(),trusted_prebuilt_cache=True,mathlib_revision='d13f23b723b8a846827a245b89c10fc7d3f11612',lean_version=subprocess.run([lean,'--version'],capture_output=True,text=True).stdout.strip(),ru_maxrss_children_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
(root/'replay-result.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2));raise SystemExit(p.returncode)
