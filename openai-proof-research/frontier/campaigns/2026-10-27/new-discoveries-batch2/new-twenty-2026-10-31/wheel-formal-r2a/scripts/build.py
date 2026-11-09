from pathlib import Path
import os,sys,subprocess
D=Path(__file__).resolve().parent.parent
os.chdir(D)
e=dict(os.environ,LEAN_PATH=(D/'lean-path.txt').read_text())
lean='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
for m in sys.argv[1:]:
 p=subprocess.run([sys.executable,'scripts/guard.py','logs/dev-'+m+'.log',lean,'-j1','-DwarningAsError=true','-o','formal/'+m+'.olean','formal/'+m+'.lean'],env=e)
 print((D/('logs/dev-'+m+'.log')).read_text()[-12000:])
 if p.returncode:sys.exit(p.returncode)
