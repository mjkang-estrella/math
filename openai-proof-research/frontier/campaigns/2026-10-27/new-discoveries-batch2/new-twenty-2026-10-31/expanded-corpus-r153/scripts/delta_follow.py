import pathlib,json,runpy
L=pathlib.Path(__file__).resolve().parents[1]
rows=json.loads((L/'outputs/delta.json').read_text())
print('graphs',len(rows),'moves',sum(r['trial_expansion_greedy_moves'] for r in rows))
for r in rows:
 if r['smallest_order_found']<r['pure_minimum_order']: print(json.dumps(r))
