import sys,pathlib,json,re,time
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from net import get,D
if sys.argv[1]=='versions':
 for p in sorted((D/'sources').glob('*-abs.html')):
  if not re.match(r'\d{4}\.\d',p.name):continue
  text=p.read_text();versions=sorted(set(re.findall(r'/abs/(\d{4}\.\d+v\d+)',text)))
  print(p.name,versions,flush=True)
  for v in versions:get(v+'.pdf','https://arxiv.org/pdf/'+v)
if sys.argv[1]=='registries':
 for key,repo in [('pool','Vilin97/lean-pool'),('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
  head=json.loads((D/f'sources/{key}-head.json').read_text())['sha'];get(key+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{head}?recursive=1')
 head=json.loads((D/'sources/pool-head.json').read_text())['sha']
 tree=json.loads((D/'sources/pool-tree.json').read_text())
 for o in tree.get('tree',[]):
  if o['type']=='blob' and (o['path']=='projects.yml' or o['path'].startswith('candidates/')):get('pool-'+o['path'].replace('/','_'),f'https://raw.githubusercontent.com/Vilin97/lean-pool/{head}/'+o['path'])
