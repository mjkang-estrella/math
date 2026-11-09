import pathlib,sys,json,time,urllib.parse
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
out={'heads':{},'receipts':[],'queries':[]}
for repo in ['Vilin97/lean-pool','openai/math','the-omega-institute/trureturing']:
 z=fetch('https://api.github.com/repos/'+repo+'/commits/HEAD','head-'+repo.split('/')[0]);out['receipts'].append(z)
 if z['status']==200:out['heads'][repo]=json.loads(pathlib.Path(z['body']).read_text())['sha']
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2))
for repo,sha in out['heads'].items():
 z=fetch(f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1','tree-'+repo.split('/')[0]);out['receipts'].append(z)
 if repo=='Vilin97/lean-pool' and z['status']==200:
  for n,x in enumerate(json.loads(pathlib.Path(z['body']).read_text())['tree']):
   p=x['path']
   if p=='projects.yml' or (p.startswith('candidates/') and x['type']=='blob'):
    out['receipts'].append(fetch(f'https://raw.githubusercontent.com/{repo}/{sha}/{p}','pool-'+str(n)))
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2));print(out['heads'])
