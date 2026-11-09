import json,pathlib
L=pathlib.Path(__file__).resolve().parents[1]
o=json.loads((L/'sources/omega-root.json').read_text())
for x in o['tree']:
 if x['path'] in ['D5','Problems']:print(x['path'],x['sha'])
for s in ['omega','openai']:print(s,json.loads((L/f'sources/{s}-head.json').read_text())['sha'])
