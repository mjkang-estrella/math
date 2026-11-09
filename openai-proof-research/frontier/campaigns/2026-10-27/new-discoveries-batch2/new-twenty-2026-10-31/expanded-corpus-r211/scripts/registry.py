exec(compile((__import__('pathlib').Path(__file__).resolve().parent/'fetch.py').read_text(),str(__import__('pathlib').Path(__file__).resolve().parent/'fetch.py'),'exec'))
for key,repo in [('leanpool','Vilin97/lean-pool'),('openai','openai/math'),('omega','the-omega-institute/trureturing')]:
 sha=json.loads((D/'sources'/f'{key}-head.json').read_text())['sha'];get(key+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1')
 if key=='leanpool':get('leanpool-projects.yml',f'https://raw.githubusercontent.com/{repo}/{sha}/projects.yml')
p=D/'sources/leanpool-tree.json'
if p.exists():
 sha=json.loads((D/'sources/leanpool-head.json').read_text())['sha']
 for x in json.loads(p.read_text()).get('tree',[]):
  if x['type']=='blob' and x['path'].startswith('candidates/'):
   get('leanpool-candidate-'+x['path'].replace('/','_'),f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/'+x['path'])
