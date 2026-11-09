from pathlib import Path
import json
L=Path(__file__).parent
for name in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative/new-discoveries-batch2'/name).read_text())
 print(name,'keys',list(d))
 for a in d.get('accepted',[]): print(a.get('number'),a.get('title'),a.get('scope'))
 for k,v in d.items():
  if k!='accepted': print(k,str(v)[:4500])
