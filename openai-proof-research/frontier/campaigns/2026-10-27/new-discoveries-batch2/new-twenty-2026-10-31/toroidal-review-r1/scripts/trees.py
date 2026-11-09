import json,pathlib
L=pathlib.Path(__file__).resolve().parents[1]
for name in ['omega-root','openai-root']:
 d=json.loads((L/'downloads'/name/'body').read_text()); print(name,'truncated',d.get('truncated'))
 for r in d['tree']:
  if r['type']=='tree': print(r['path'],r['sha'])
print('citing',json.loads((L/'downloads/openalex-citing/body').read_text())['meta'])
