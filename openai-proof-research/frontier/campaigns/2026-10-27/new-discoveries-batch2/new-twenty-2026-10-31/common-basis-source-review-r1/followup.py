from pathlib import Path
import json,runpy
L=Path(__file__).resolve().parent;fetch=runpy.run_path(str(L/'fetch.py'))['fetch']
h=json.loads((L/'receipts/pool-head.json').read_text())['sha'];t=json.loads((L/'pool-paths.json').read_text())
for e in t:
 p=e['path']
 if e['type']=='blob' and 'TuttePath' in p and p.endswith(('.lean','.tex','.md')):fetch('pool--'+p.replace('/','__'),'https://raw.githubusercontent.com/Vilin97/lean-pool/'+h+'/'+p)
for p in (L/'receipts').glob('*sub-*.json'):
 try:d=json.loads(p.read_text());print(p.name,'truncated',d.get('truncated'),'entries',len(d.get('tree',[])))
 except:pass
for tag in ['openai','omega']:
 d=json.loads((L/(tag+'-paths.json')).read_text());matches=[e['path'] for e in d if any(w in e['path'].lower() for w in ['matroid','lason','332371','complementary.bas'])];(L/(tag+'-matches.json')).write_text(json.dumps(matches,indent=2));print(tag,len(matches))
