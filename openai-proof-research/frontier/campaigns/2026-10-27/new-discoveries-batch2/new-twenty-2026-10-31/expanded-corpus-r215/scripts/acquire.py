import pathlib,json,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]
def get(n,u):subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),n,u],check=True)
mode=sys.argv[1]
if mode=='sources':
 seen=set()
 for o in json.loads((D/'extracted.json').read_text()).values():
  a=o['source_url'].split('/')[-1]
  if a in seen:continue
  seen.add(a);get(a+'.abs','https://arxiv.org/abs/'+a)
  get(a+'.pdf','https://arxiv.org/pdf/'+a)
elif mode=='registries':
 for label,repo in [('leanpool','Vilin97/lean-pool'),('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
  sha=json.loads((D/'sources'/f'{label}-head.json').read_text())['sha']
  print(label,sha,flush=True)
  get(label+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1')
  if label=='leanpool':get('leanpool-projects.yml',f'https://raw.githubusercontent.com/{repo}/{sha}/projects.yml')
