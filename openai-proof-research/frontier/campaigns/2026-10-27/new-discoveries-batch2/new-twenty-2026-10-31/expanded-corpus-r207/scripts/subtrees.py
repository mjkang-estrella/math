from pathlib import Path
import json,importlib.util
L=Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('f',L/'scripts/fetch.py'); f=importlib.util.module_from_spec(s);s.loader.exec_module(f)
R=json.loads((L/'outputs/registry-screen.json').read_text())
for kind,repo,paths in [('omega','the-omega-institute/trureturing',['D5','Problems']),('openai','openai/math',['preprints'])]:
 for path in paths:
  tree=json.loads((Path(R[kind]['tree_receipt'])/'body').read_text())['tree']; ent=next((x for x in tree if x['path']==path),None)
  if ent:
   b,r,p=f.fetch(f'https://api.github.com/repos/{repo}/git/trees/{ent["sha"]}?recursive=1',kind+'-'+path);R[kind][path]={'receipt':p,'truncated':json.loads(b).get('truncated')}
(L/'outputs/registry-screen.json').write_text(json.dumps(R,indent=2))
