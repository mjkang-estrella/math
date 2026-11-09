# Run pinned Lean 4.34.1 on a file in lean/ with pinned mathlib oleans (read-only), -M3500, warnings as errors.
import os,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1]
root=pathlib.Path('/home/mj-kang/Documents/Dev/math')
pkgs=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
lp=str(D/'lean')+':'+':'.join(str(p) for p in sorted(pkgs.glob('*/.lake/build/lib/lean')))
bin=root/'dlp-research/.tools/lean-4.34.1-linux/bin/lean'
env={'LEAN_PATH':lp,'PATH':'/usr/bin:/bin','LANG':'C.UTF-8','HOME':str(D/'lean')}
os.chdir(D/'lean')
os.execve(str(bin),[str(bin),'-j1','-M3500','-DwarningAsError=true',*sys.argv[1:]],env)
