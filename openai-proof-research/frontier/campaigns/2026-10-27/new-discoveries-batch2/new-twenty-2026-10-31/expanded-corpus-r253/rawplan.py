from pathlib import Path
import json
L=Path(__file__).resolve().parent;t=json.loads((L/'http/pool-tree.json').read_text());j=[]
for x in t['tree']:
 if x['path'].startswith('candidates/'):
  print(x['path'],x.get('size'))
  if x['type']=='blob' and x['path'].endswith(('.jsonl','.csv','.tsv','.json','.yml','.txt')):j.append(['pool-'+x['path'].replace('/','_'),'https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/'+x['path']])
(L/'raw-plan.json').write_text(json.dumps(j))
