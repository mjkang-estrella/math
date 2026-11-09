from pathlib import Path
import json,subprocess,sys
r=Path(__file__).resolve().parent.parent
for m in json.loads((r/'outputs/new-modules-r4.json').read_text()):
 p=subprocess.run([str(r/'scripts/lean.sh'),'-o',str(r/f'build/{m}.olean'),m+'.lean'],stdout=subprocess.PIPE,text=True)
 if p.returncode: print(p.stdout);sys.exit(p.returncode)
 print('BUILT '+m,flush=True)
