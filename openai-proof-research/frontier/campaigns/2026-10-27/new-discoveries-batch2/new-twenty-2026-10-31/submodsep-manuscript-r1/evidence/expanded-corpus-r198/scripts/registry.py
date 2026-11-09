import pathlib,sys,json,re,time,urllib.parse
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
out={'heads':{},'receipts':[],'queries':[]}
for repo in ['Vilin97/lean-pool','openai/math','the-omega-institute/trureturing']:
 z=fetch('https://api.github.com/repos/'+repo+'/commits/HEAD','registry-head-'+repo.split('/')[0]);out['receipts'].append(z)
 if z['status']==200:out['heads'][repo]=json.loads(pathlib.Path(z['body']).read_text())['sha']
sha=out['heads'].get('Vilin97/lean-pool')
if sha:
 z=fetch(f'https://api.github.com/repos/Vilin97/lean-pool/git/trees/{sha}?recursive=1','pool-tree');out['receipts'].append(z)
 if z['status']==200:
  paths=[x['path'] for x in json.loads(pathlib.Path(z['body']).read_text())['tree'] if x['path']=='projects.yml' or (x['path'].startswith('candidates/') and x['type']=='blob')]
  for n,p in enumerate(paths):out['receipts'].append(fetch(f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/{p}','pool-file-'+str(n)))
queries=['"2006.00801" lean','"1902.04740" lean','"Tenner" "Glaisher" lean','"Kreweras" "evacuation" lean','"Su" "Schur" lean','"small doubling" "cyclic" lean','"strong synchronisation" lean','"fullerene" "volume" lean']
for q in queries:
 z=fetch('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),'github-search');out['queries'].append({'query':q,'receipt':z})
 if z['status']!=200:break
 time.sleep(7)
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2))
print(out['heads']);print('queries',len(out['queries']))
