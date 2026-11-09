from pathlib import Path
import json,importlib.util
L=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('lane_fetch',L/'scripts/fetch.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
t=json.loads((L/'outputs/Vilin97-lean-pool-tree.json').read_text());sha=json.loads((L/'outputs/Vilin97-lean-pool-head.json').read_text())['sha']
paths=[x['path'] for x in t['tree'] if x['path'].endswith('projects.yml') or x['path'].startswith('candidates/') or '/candidates/' in x['path']]
print('pool paths',len(paths),paths[:15])
for p in paths:
 b=m.fetch('https://raw.githubusercontent.com/Vilin97/lean-pool/'+sha+'/'+p,'pool-'+p.replace('/','-'))
 if b:(L/'sources'/('pool-'+p.replace('/','-'))).write_bytes(b)
terms=['341836','1902.04055','pancake','374163','2604.12557','missing','Sundaram','1808.01416','Hepp','Wormald','Schmidt','detachable','MIMO','overpartition','cubic partition','second neighbor']
out={}
for p in (L/'outputs').glob('*-tree.json'):
 t=json.loads(p.read_text());out[p.name]={'truncated':t.get('truncated'),'hits':[x['path'] for x in t.get('tree',[]) if any(w.lower() in x['path'].lower() for w in terms)]}
(L/'outputs/registry-path-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2)[:5000])
