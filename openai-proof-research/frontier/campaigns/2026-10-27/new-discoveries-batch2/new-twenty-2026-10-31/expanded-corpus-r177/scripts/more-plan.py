import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1];todo=[]
for a in ['2411.12917','2603.11883','2610.19014','2509.17326']:todo.append([a+'.pdf','https://arxiv.org/pdf/'+a])
# All historical versions for source fidelity, no repeated latest fetch.
for o in json.loads((D/'extracted.json').read_text()).values():
 a=o['source_url'].rsplit('/',1)[-1];s=(D/'sources'/f'{a}.abs.html').read_text();vs=sorted(set(re.findall(r'\[v(\d+)\]',s)),key=int)
 for v in vs[:-1]:todo.append([a+'v'+v+'.pdf','https://arxiv.org/pdf/'+a+'v'+v])
(D/'outputs/more-plan.json').write_text(json.dumps(todo))
