import json,subprocess,sys,time
from pathlib import Path
D=Path(__file__).resolve().parents[1]
for m in json.loads((D/'manifest.json').read_text())['modules']:
 if (D/f'PDTAR/{m}.olean').exists(): continue
 r=subprocess.run([sys.executable,'-I','scripts/limited.py',str(time.time_ns())+'-dev-'+m,sys.executable,'-I','scripts/compile.py','-o',f'PDTAR/{m}.olean',f'PDTAR/{m}.lean'],cwd=D)
 if r.returncode: sys.exit(r.returncode)
