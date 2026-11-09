from pathlib import Path
import json,importlib.util,re
L=Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('fetch',L/'scripts/fetch.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
for name,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 t=json.loads((L/'sources'/f'{name}-root.json').read_text());print(name,[(x['path'],x['type']) for x in t['tree']])
 for x in t['tree']:
  if x['path'] in ['Problems','preprints']:
   b=m.fetch('https://api.github.com/repos/'+repo+'/git/trees/'+x['sha']+'?recursive=1',name+'-'+x['path'])
   if b:(L/'sources'/f'{name}-{x["path"]}.json').write_bytes(b)
terms=['pancake','missinginteger','MissingInteger','Sundaram','ParityRestricted','Hepp','Wormald','SecondNeighborhood','BlindMIMO','Overpartition','Detachable']
for p in list((L/'sources').glob('omega-*.json'))+list((L/'sources').glob('openai-*.json')):
 d=json.loads(p.read_text());hits=[x['path'] for x in d.get('tree',[]) if any(w.lower() in x['path'].lower() for w in terms)];print(p.name,'truncated',d.get('truncated'),'hits',hits[:50])
