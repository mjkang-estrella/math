import pathlib,json,collections
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'outputs/weights.json').read_text());c=collections.Counter(h['q'] for h in x['hits']);print('hits',len(x['hits']),dict(c));print('first',[(h['q'],h['ell'],h['m'],h['t']) for h in x['hits'][:12]])
r=json.loads((D/'outputs/registry-screen.json').read_text())
for k in ['omega','openai']:
 print(k,'truncated',r[k]['truncated']);print([p for p in r[k]['path_hits'] if any(s in p.lower() for s in ['determinantal','seacrest','yancey','kriesell','wronskian','fromentin','inducibility'])][:12])
