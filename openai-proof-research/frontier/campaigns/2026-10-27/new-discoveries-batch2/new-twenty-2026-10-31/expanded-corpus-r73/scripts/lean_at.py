# Run pinned Lean (-j1 strict) in a given directory with that directory first on LEAN_PATH.
import os,pathlib,sys
root=pathlib.Path('/home/mj-kang/Documents/Dev/math')
pkgs=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
d=pathlib.Path(sys.argv[1]).resolve()
lp=str(d)+':'+':'.join(str(p) for p in sorted(pkgs.glob('*/.lake/build/lib/lean')))
binp=root/'dlp-research/.tools/lean-4.34.1-linux/bin'/sys.argv[2]
os.environ.clear(); os.environ.update({'LEAN_PATH':lp,'PATH':'/usr/bin:/bin','LANG':'C.UTF-8','LEAN_NUM_THREADS':'1','MALLOC_ARENA_MAX':'2'})
os.chdir(d)
args=sys.argv[3:]
if sys.argv[2]=='lean': args=['-j1','-DwarningAsError=true',*args]
os.execv(str(binp),[str(binp),*args])
