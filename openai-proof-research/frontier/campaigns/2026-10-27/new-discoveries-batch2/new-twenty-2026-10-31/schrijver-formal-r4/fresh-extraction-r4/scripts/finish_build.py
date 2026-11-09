from pathlib import Path
import json,subprocess,sys
r=Path(__file__).resolve().parent.parent
mods=['TableLinks']+[m for m in json.loads((r/'outputs/table-modules.json').read_text()) if m.startswith('Link28_') and int(m.split('_')[1])>=99]+['Table28','UpperTrees','BridgeTransport']
for m in mods:
 p=subprocess.run([sys.executable,'-I',str(r/'scripts/build_selected.py'),m])
 if p.returncode:sys.exit(p.returncode)
