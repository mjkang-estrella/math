#!/usr/bin/env python3
from pathlib import Path
import os,sys,subprocess
D=Path(__file__).resolve().parent.parent
os.chdir(D)
lean='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
packages=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env=dict(os.environ,LEAN_PATH=str(D/'formal')+':'+':'.join(str(p/'.lake/build/lib/lean') for p in packages.iterdir() if (p/'.lake/build/lib/lean').is_dir()),MALLOC_ARENA_MAX='2',TMPDIR=str(D/'tmp'))
for mod in sys.argv[1:]:
 old=D/'logs'/(mod+'.log')
 if old.exists():
  n=1
  while (D/'logs'/(mod+'.attempt'+str(n)+'.log')).exists():n+=1
  old.rename(D/'logs'/(mod+'.attempt'+str(n)+'.log'))
  receipt=old.with_suffix('.log.receipt.json')
  if receipt.exists():receipt.rename(D/'logs'/(mod+'.attempt'+str(n)+'.log.receipt.json'))
 args=[lean,'-j1','-DwarningAsError=true','-o',str(D/'formal'/(mod+'.olean')),str(D/'formal'/(mod+'.lean'))]
 r=subprocess.run([sys.executable,'scripts/guard.py',str(D/'logs'/(mod+'.log'))]+args,env=env)
 print((D/'logs'/(mod+'.log')).read_text()[-18000:])
 if r.returncode:sys.exit(r.returncode)
