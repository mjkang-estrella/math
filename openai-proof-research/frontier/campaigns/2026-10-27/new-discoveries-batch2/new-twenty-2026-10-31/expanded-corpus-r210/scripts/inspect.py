from pathlib import Path
import json,re
L=Path(__file__).resolve().parents[1]
for repo in ['Vilin97-lean-pool','openai-math','the-omega-institute-trureturing']:
 d=json.loads((L/'outputs'/f'{repo}-head.json').read_text());print(repo,d['sha'])
 t=json.loads((L/'outputs'/f'{repo}-tree.json').read_text())
 print([(x['path'],x['sha']) for x in t['tree'] if x['type']=='tree' and x['path'] in ['preprints','Problems','D5','LeanPool']])
for p in (L/'sources').glob('pool-*'):
 lines=p.read_text(errors='replace').splitlines()
 for i,s in enumerate(lines):
  if re.search('1902.04055|2604.12557|1808.01416|1810.07856|Sundaram|pancake|Wormald|Hepp|second neighborhood',s,re.I):print(p.name,i+1,s[:250])
