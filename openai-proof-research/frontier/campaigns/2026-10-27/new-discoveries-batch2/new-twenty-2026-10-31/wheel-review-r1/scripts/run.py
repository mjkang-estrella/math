from pathlib import Path
import os,sys
D=Path(__file__).resolve().parent.parent
os.chdir(D)
bin=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
pkgs=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
os.environ['PATH']=str(bin)+':'+os.environ.get('PATH','/usr/bin:/bin')
os.environ.update(LEAN_PATH=str(D/'replay/formal')+':'+':'.join(str(x/'.lake/build/lib/lean') for x in pkgs.iterdir() if (x/'.lake/build/lib/lean').is_dir()),MALLOC_ARENA_MAX='2',TMPDIR=str(D/'tmp'),PYTHONDONTWRITEBYTECODE='1')
mode,name=sys.argv[1:]
if mode=='build':args=[str(bin/'lean'),'-j1','-DwarningAsError=true','-o',str(D/'replay/formal'/(name+'.olean')),str(D/'replay/formal'/(name+'.lean'))]
elif mode=='check':args=[str(bin/'leanchecker'),name]
else:args=[str(bin/'lean'),'-j1','-DwarningAsError=true',str(D/'replay/formal'/(name+'.lean'))]
os.execvp('systemd-run',['systemd-run','--user','--scope','-p','MemoryMax=6G',sys.executable,'-I',str(D/'scripts/guard.py'),str(D/'logs'/(mode+'-'+name+'.log'))]+args)
