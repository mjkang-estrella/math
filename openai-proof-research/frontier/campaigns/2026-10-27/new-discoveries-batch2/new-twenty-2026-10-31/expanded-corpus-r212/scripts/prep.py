import json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
for n in ['pool','omega','openai']:
 j=json.loads((D/f'sources/{n}-head.json').read_text());print(n,j['sha'])
r=json.loads((D/'extracted.json').read_text())
for i,o in r.items():print(i,o['source_url'])
