import os,subprocess,sys
from pathlib import Path
p=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env=dict(os.environ,LEAN_PATH=':'.join(str(x/'.lake/build/lib/lean') for x in p.iterdir() if x.is_dir()))
r=subprocess.run(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean',*sys.argv[1:]],env=env)
sys.exit(r.returncode)
