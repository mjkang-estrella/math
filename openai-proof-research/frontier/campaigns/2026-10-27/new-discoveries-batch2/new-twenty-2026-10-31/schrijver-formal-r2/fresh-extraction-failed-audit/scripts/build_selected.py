from pathlib import Path
import sys,subprocess
r=Path(__file__).resolve().parent.parent
for m in sys.argv[1:]:
 p=subprocess.run([str(r/'scripts/lean.sh'),'-o',str(r/f'build/{m}.olean'),m+'.lean'])
 if p.returncode:sys.exit(p.returncode)
 print('BUILT '+m,flush=True)
