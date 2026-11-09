from pathlib import Path
import os, subprocess, json, hashlib, time, resource
r=Path(__file__).resolve().parent; e=r/'clean'; s=r.parent/'intricacy-entropy-r5'
mods=['Target333569','Algebra333569','Curvature333569','Cylinders333569','Diagonal333569','SeriesCurvature333569','Entropy333569','Consistency333569','TwoSided333569','Stationarity333569','FiniteEntropy333569','Selected333569','SelectedEntropy333569','FairSelections333569','FairEntropy333569','EntropyLimit333569','TransverseEntropy333569','SeriesDerivatives333569','ParameterMaximum333569','SourceParameter333569','WeakMarkov333569']
lean='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
cache=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
packages=['mathlib','plausible','LeanSearchClient','importGraph','proofwidgets','aesop','Qq','batteries']
env={'PATH':'/usr/bin:/bin','HOME':str(r),'LANG':'C.UTF-8','LEAN_PATH':':'.join([str(e)]+[str(cache/p/'.lake/build/lib/lean') for p in packages])}
def limits():
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(180,180));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
p=subprocess.run([lean,'-j2','-M4096','-DwarningAsError=true','IndependentInventory.lean'],cwd=e,env=env,preexec_fn=limits,capture_output=True,text=True,timeout=240)
(r/'complete-inventory.log').write_text(p.stdout+p.stderr)
print(p.returncode);print((p.stdout+p.stderr)[-4000:])
