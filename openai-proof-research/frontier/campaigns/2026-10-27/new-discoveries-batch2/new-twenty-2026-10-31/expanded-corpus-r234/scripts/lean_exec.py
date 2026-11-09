import os,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1];P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages');bin=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
root=pathlib.Path(sys.argv[1]).resolve(); mode=sys.argv[2]
env={'LEAN_PATH':str(root)+':'+':'.join(str(p/'.lake/build/lib/lean') for p in P.iterdir()),'PATH':str(bin)+':/usr/bin:/bin','LANG':'C.UTF-8','MALLOC_ARENA_MAX':'2','TMPDIR':str(D/'tmp')}
os.environ.clear();os.environ.update(env);os.chdir(root)
if mode=='lean':os.execv(str(bin/'lean'),[str(bin/'lean'),'-j1','-M3500','-DwarningAsError=true',*sys.argv[3:]])
else:os.execv(str(bin/'leanchecker'),[str(bin/'leanchecker'),*sys.argv[3:]])
