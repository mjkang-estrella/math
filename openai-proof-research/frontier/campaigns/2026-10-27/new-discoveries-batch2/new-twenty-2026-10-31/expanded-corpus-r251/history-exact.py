from pathlib import Path
import json,re
L=Path(__file__).resolve().parent
x=json.loads((L/'historical-screen.json').read_text())
for i,ls in x.items():
 for a in ls:a['classification']='incidental hash/digit substring; no historical reserved-record review inferred'
# Add actual inherited family audit rather than accidental hash matches.
x['334350'].append({'file':'../expanded-corpus-r215/results.json','classification':'same source family 334353 held; binding TASK HOLD retained'})
for i in ('334351','334352'):x[i].append(x['334350'][-1])
x['334561'].append({'file':'../expanded-corpus-r215/results.json','classification':'same equi-n-square obstruction already excluded for a different reserved record; Pokrovskiy-Sudakov theorem retained'})
(L/'historical-screen.json').write_text(json.dumps(x,indent=2))
