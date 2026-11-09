# Run the pinned Lean 4.34.1 binary against the read-only cached mathlib oleans, strict warnings-as-errors.
import os,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1]
root=pathlib.Path('/home/mj-kang/Documents/Dev/math')
pkgs=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
lp=str(D/'formal/build')+':'+':'.join(str(p) for p in sorted(pkgs.glob('*/.lake/build/lib/lean')))
binp=root/'dlp-research/.tools/lean-4.34.1-linux/bin/lean'
os.environ.clear(); os.environ.update({'LEAN_PATH':lp,'PATH':'/usr/bin:/bin','LANG':'C.UTF-8'})
os.chdir(D/'formal')
os.execv(str(binp),[str(binp),'-j2','-DwarningAsError=true',*sys.argv[1:]])
