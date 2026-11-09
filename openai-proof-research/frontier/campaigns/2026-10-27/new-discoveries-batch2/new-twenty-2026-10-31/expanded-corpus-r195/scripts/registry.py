import json,pathlib,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
def get(n,u):subprocess.run(['python3','-I',str(D/'scripts/fetch.py'),n,u],check=True)
for n,repo in [('pool','Vilin97/lean-pool'),('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 h=json.loads((D/f'sources/{n}-head.body').read_text())['sha']; print(n,h,flush=True)
 get(n+'-tree',f'https://api.github.com/repos/{repo}/git/trees/{h}?recursive=1')
 if n=='pool':
  t=json.loads((D/f'sources/{n}-tree.body').read_text())
  for j,z in enumerate(t.get('tree',[])):
   p=z['path']
   if p=='projects.yml' or (p.startswith('candidates/') and z['type']=='blob'):
    get('pool-file-'+str(j),f'https://raw.githubusercontent.com/{repo}/{h}/{p}')
