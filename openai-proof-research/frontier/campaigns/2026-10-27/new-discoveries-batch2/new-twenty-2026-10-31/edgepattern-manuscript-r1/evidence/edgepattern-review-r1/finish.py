from pathlib import Path
import subprocess,os,sys,json
b=Path(__file__).resolve().parent;f=b/'fresh'
r=json.loads((f/'replay-receipt.json').read_text());assert r['passed'], 'Full replay must finish first'
env=os.environ.copy();env.update(LEAN_BIN='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean',LEAN_PACKAGES='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages',MALLOC_ARENA_MAX='2')
for s in ['negative.py','check-auditor.py']:
 with (b/('driver-'+s+'.log')).open('w') as out:
  r=subprocess.run([sys.executable,'-I','scripts/'+s],cwd=f,env=env,stdout=out,stderr=subprocess.STDOUT)
 assert r.returncode==0,(s,r.returncode)
subprocess.run([sys.executable,'-I',str(b/'finalize_checks.py')],cwd=b,env=env,check=True)
