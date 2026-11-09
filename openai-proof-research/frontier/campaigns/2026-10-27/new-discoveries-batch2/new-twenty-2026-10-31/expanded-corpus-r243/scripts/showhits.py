import pathlib,json
L=pathlib.Path(__file__).resolve().parents[1];x=json.loads((L/'evidence/complete-registry-path-screen.json').read_text())
for k,v in x.items():
 print(k,v['truncated'],v['count'])
 print('\n'.join(p for p in v['hits'] if 'FibonacciAtomic' not in p)[:17000])
