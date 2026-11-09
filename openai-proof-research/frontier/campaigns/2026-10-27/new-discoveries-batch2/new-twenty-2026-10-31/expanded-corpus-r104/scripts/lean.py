# Usage: lean.py Module.Path  -> compiles formal/Module/Path.lean to formal/build/Module/Path.olean (strict warnings-as-errors)
import os,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1]
root=pathlib.Path('/home/mj-kang/Documents/Dev/math')
pkgs=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
build=pathlib.Path(os.environ.get('SSA_BUILD',str(D/'formal/build'))); src=pathlib.Path(os.environ.get('SSA_SRC',str(D/'formal')))
mod=sys.argv[1]; rel=mod.replace('.','/')
(build/rel).parent.mkdir(parents=True,exist_ok=True)
lp=str(build)+':'+':'.join(str(p) for p in sorted(pkgs.glob('*/.lake/build/lib/lean')))
bin=root/'dlp-research/.tools/lean-4.34.1-linux/bin/lean'
os.environ.clear();os.environ.update({'LEAN_PATH':lp,'PATH':'/usr/bin:/bin','LANG':'C.UTF-8','TMPDIR':str(D/'tmp')})
os.chdir(src)
os.execv(str(bin),[str(bin),'-j2','-DwarningAsError=true','-o',str(build/(rel+'.olean')),'-i',str(build/(rel+'.ilean')),*sys.argv[2:],rel+'.lean'])
