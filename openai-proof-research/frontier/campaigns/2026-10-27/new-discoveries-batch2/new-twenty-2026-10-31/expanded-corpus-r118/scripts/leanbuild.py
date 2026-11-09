# Strict build to .olean, then leanchecker replay of the module (pinned toolchain, read-only mathlib).
import os,pathlib,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]; L=D/'lean' if len(sys.argv)<3 else pathlib.Path(sys.argv[2])
root=pathlib.Path('/home/mj-kang/Documents/Dev/math'); bin=root/'dlp-research/.tools/lean-4.34.1-linux/bin'
pkgs=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
env={'LEAN_PATH':str(L)+':'+':'.join(str(p) for p in sorted(pkgs.glob('*/.lake/build/lib/lean'))),'PATH':str(bin)+':/usr/bin:/bin','LANG':'C.UTF-8','HOME':str(L)}
m=sys.argv[1]
r1=subprocess.run([str(bin/'lean'),'-j1','-M3500','-DwarningAsError=true','-o',f'{m}.olean',f'{m}.lean'],cwd=L,env=env)
print('strict build rc',r1.returncode,flush=True)
if r1.returncode: sys.exit(r1.returncode)
r2=subprocess.run([str(bin/'leanchecker'),m],cwd=L,env=env)
print('leanchecker rc',r2.returncode,flush=True); sys.exit(r2.returncode)
