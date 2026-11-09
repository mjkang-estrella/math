import json,importlib.util
from pathlib import Path
L=Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('f',L/'scripts/fetch.py');f=importlib.util.module_from_spec(s);s.loader.exec_module(f);R=json.loads((L/'outputs/registry-screen.json').read_text())
for kind,repo,scope in [('omega','the-omega-institute/trureturing','Problems'),('openai','openai/math','preprints')]:
 b,r,p=f.fetch(f'https://api.github.com/repos/{repo}/git/trees/{R[kind]["head"]}',kind+'-root');d=json.loads(b)
 e=next((x for x in d.get('tree',[]) if x['path']==scope),None)
 if e:
  b,r,p=f.fetch(f'https://api.github.com/repos/{repo}/git/trees/{e["sha"]}?recursive=1',kind+'-'+scope);R[kind][scope]={'receipt':p,'truncated':json.loads(b).get('truncated')}
(L/'outputs/registry-screen.json').write_text(json.dumps(R,indent=2))
