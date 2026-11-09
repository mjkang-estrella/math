import importlib.util,json,pathlib
print({x:bool(importlib.util.find_spec(x)) for x in ['z3','scipy','sympy','numpy','networkx']})
L=pathlib.Path(__file__).resolve().parents[1]
for x in ['omega','openai']:
 r=json.loads((L/f'sources/{x}-head.json').read_text());print(x,r['sha'])
for p in ['ledger-read','current-ledger-read','context-read']:
 r=json.loads((L/f'outputs/{p}.json').read_text())
 print(p)
 for k in ['accepted','excluded','held_candidates']:
  for v in r.get(k,[]):print(k, json.dumps(v,ensure_ascii=False)[:350])
