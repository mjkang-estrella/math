import os,subprocess,resource,time,json,hashlib
from pathlib import Path
p=Path(__file__).resolve().parent
pk=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
lean='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
os.environ['LEAN_PATH']=':'.join(str(x/'.lake/build/lib/lean') for x in pk.iterdir())
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120))
t=time.monotonic();args=[lean,'-j1','-M2048','-DwarningAsError=true',str(p/'DualPolar.lean')]
r=subprocess.run(args,capture_output=True,text=True,timeout=130);(p/'replay.log').write_text(r.stdout+r.stderr)
receipt={'returncode':r.returncode,'command':args,'wall_s':time.monotonic()-t,'affinity':sorted(os.sched_getaffinity(0)),'managed_heap_limit_MiB':2048,'cpu_limit_s':120,'maxrss_children_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'source_sha256':hashlib.sha256((p/'DualPolar.lean').read_bytes()).hexdigest(),'cache_trust':'Pinned prebuilt mathlib oleans trusted; no independent rebuild of dependency cache; Lean kernel checks new proofs. Initial RLIMIT_AS runs failed to create threads; this run uses Lean managed-memory limit.'}
(p/'receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt));print(r.stdout+r.stderr)
