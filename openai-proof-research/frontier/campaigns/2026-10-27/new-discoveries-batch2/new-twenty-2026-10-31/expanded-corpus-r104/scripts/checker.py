# Usage: checker.py Module -> runs leanchecker on a module against replay/build + pinned mathlib oleans
import os,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1]
root=pathlib.Path('/home/mj-kang/Documents/Dev/math')
pkgs=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
binp=root/'dlp-research/.tools/lean-4.34.1-linux/bin'
build=D/'replay/build'
lp=str(build)+':'+':'.join(str(p) for p in sorted(pkgs.glob('*/.lake/build/lib/lean')))
os.environ.clear();os.environ.update({'LEAN_PATH':lp,'PATH':str(binp)+':/usr/bin:/bin','LANG':'C.UTF-8','TMPDIR':str(D/'tmp')})
os.chdir(build)
os.execv(str(binp/'leanchecker'),[str(binp/'leanchecker'),sys.argv[1]])
