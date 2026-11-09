import os,pathlib,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]
root=pathlib.Path('/home/mj-kang/Documents/Dev/math')
pkgs=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
os.environ['LEAN_PATH']=str(D/'fresh-replay')+':' + ':'.join(str(p) for p in pkgs.glob('*/.lake/build/lib/lean'))
bin=root/'dlp-research/.tools/lean-4.34.1-linux/bin/lean'
keep={'LEAN_PATH':os.environ['LEAN_PATH'],'PATH':'/usr/bin:/bin','LANG':'C.UTF-8'}
os.environ.clear();os.environ.update(keep)
os.chdir(D/'fresh-replay')
os.execv(str(bin),[str(bin),'-j1','-DwarningAsError=true',*sys.argv[1:]])
