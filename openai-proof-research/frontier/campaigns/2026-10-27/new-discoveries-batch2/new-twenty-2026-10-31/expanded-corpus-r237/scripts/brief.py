from pathlib import Path
import json,re
L=Path(__file__).resolve().parents[1]
for k in ['openai','omega']:
 d=json.loads((L/f'sources/{k}-tree.json').read_text());print(k,'truncated',d.get('truncated'))
 for x in d.get('tree',[]):
  if re.search('Cograph|Eventown|Gonality|NeuralCode|Hyperconnectivity|RegularCharacter|CubicVertex|Entailment|PnLine|QMatroid|TriWeight|Jaeger|InfiniteHex',x['path'],re.I):print(x['path'])
print('search counts')
for p in (L/'sources').glob('github-search-?.json'):
 d=json.loads(p.read_text());print(p.name,d.get('total_count'),[x['full_name'] for x in d.get('items',[])])
