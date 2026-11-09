# Fresh extracted replay: strict build of TabMinors (warnings as errors) + leanchecker + audit, in lean-packet/ only.
import os,pathlib,subprocess,sys,hashlib,json
D=pathlib.Path(__file__).resolve().parents[1]; P=D/'lean-packet'
root=pathlib.Path('/home/mj-kang/Documents/Dev/math'); bin=root/'dlp-research/.tools/lean-4.34.1-linux/bin'
pkgs=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
env={'LEAN_PATH':str(P)+':'+':'.join(str(p) for p in sorted(pkgs.glob('*/.lake/build/lib/lean'))),'PATH':str(bin)+':/usr/bin:/bin','LANG':'C.UTF-8','HOME':str(P)}
out={'source_sha256':hashlib.sha256((P/'TabMinors.lean').read_bytes()).hexdigest(),'lean':str(bin/'lean'),'mathlib_rev':'d13f23b723b8a846827a245b89c10fc7d3f11612 (pinned cache, read-only, not rebuilt)','env_keys':sorted(env)}
for name,cmd in [('build',[str(bin/'lean'),'-j1','-M3500','-DwarningAsError=true','-o','TabMinors.olean','TabMinors.lean']),('leanchecker',[str(bin/'leanchecker'),'TabMinors']),('audit',[str(bin/'lean'),'-j1','-M3500','-DwarningAsError=true','Audit.lean'])]:
    r=subprocess.run(cmd,cwd=P,env=env,capture_output=True,text=True); out[name]={'cmd':cmd,'rc':r.returncode,'stdout':r.stdout[-3000:],'stderr':r.stderr[-2000:]}
    print(name,'rc',r.returncode,flush=True)
    if r.returncode: break
(D/'outputs/lean-packet-replay.json').write_text(json.dumps(out,indent=2)+'\n'); print(out.get('audit',{}).get('stdout','')[-800:])
