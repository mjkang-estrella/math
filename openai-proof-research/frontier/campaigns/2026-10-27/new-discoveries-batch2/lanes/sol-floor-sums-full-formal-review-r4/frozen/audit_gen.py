from pathlib import Path
import json
L=Path(__file__).resolve().parent
mods=json.loads((L/'checked-modules.json').read_text())
template=(L/'frozen/sol-floor-sums-certificate-formal-r2/Audit.lean').read_text()
body=template[template.index('import Lean\n'):]
start=body.index('if [');end=body.index('].contains',start)
audits=[]
for k in range(0,len(mods),20):
 selected=mods[k:k+20];name=f'Audit{k//20:03d}'
 b=body[:start]+'if '+json.dumps(selected)+body[end+1:]
 (L/(name+'.lean')).write_text(''.join('import '+m+'\n' for m in mods)+b)
 audits.append(name)
(L/'audit-modules.json').write_text(json.dumps(audits,indent=2)+'\n')
print('exhaustive audit partitions',len(audits),'origins',len(mods))
