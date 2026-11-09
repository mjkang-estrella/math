import pathlib,importlib.util,json
D=pathlib.Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('f',D/'scripts/fetch.py');f=importlib.util.module_from_spec(s);s.loader.exec_module(f)
for tag,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 sha=json.loads((D/'sources'/f'{tag}-head.json').read_text())['sha'];f.get(tag+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{sha}')
 p=D/'sources'/f'{tag}-tree.json'
 if p.exists():
  for o in json.loads(p.read_text()).get('tree',[]):
   if o['path'] in ['D5','Problems','preprints']:f.get(tag+'-'+o['path']+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/'+o['sha']+'?recursive=1')
