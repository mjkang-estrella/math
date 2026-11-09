from pathlib import Path
import os,subprocess,sys
p=Path('/home/mj-kang/Documents/Dev/math'); o=Path(__file__).resolve().parent; packages=p/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'; env=os.environ.copy(); env['LEAN_PATH']=':'.join([str(o)]+[str(x/'.lake/build/lib/lean') for x in packages.iterdir()]); env['LEAN_NUM_THREADS']='1'
subprocess.run(['python',str(o/'guard.py'),sys.argv[1],str(p/'dlp-research/.tools/lean-4.34.1-linux/bin/lean'),'-j1',*sys.argv[2:]],env=env,check=True)
