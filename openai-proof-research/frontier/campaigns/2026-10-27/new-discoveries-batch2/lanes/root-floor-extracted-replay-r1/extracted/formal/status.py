from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
mods=[]
for f in sorted((L/'logs').glob('*.guard.json')):
 r=json.loads(f.read_text());src=r['command'][-1]
 if r['exit_code']==0 and (L/src).with_suffix('.olean').exists():mods.append(str(Path(src).with_suffix('')).replace('/','.'))
mods=sorted(set(mods))
(L/'checked-modules.json').write_text(json.dumps(mods,indent=2)+'\n')
template=(L/'frozen/sol-floor-sums-certificate-formal-r2/Audit.lean').read_text()
body=template[template.index('import Lean\n'):]
start=body.index('if [');end=body.index('].contains',start)
body=body[:start]+'if '+json.dumps(mods)+body[end+1:]
(L/'Audit.lean').write_text(''.join('import '+m+'\n' for m in mods)+body)
print('checked modules',len(mods),'DAG',sum(m.startswith('Dag') for m in mods))
