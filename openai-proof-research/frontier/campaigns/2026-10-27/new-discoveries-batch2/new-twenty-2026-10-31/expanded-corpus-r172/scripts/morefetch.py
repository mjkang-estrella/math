import sys,pathlib,json,time,urllib.parse
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import D,fetch
mode=sys.argv[1]
if mode=='scopes':
 for repo,dirs in [('the-omega-institute/trureturing',['D5','Problems']),('openai/math',['preprints'])]:
  sha=json.loads((D/'sources'/(repo.replace('/','-')+'-head.json')).read_text())['sha'];f=repo.replace('/','-')+'-root.json';r=fetch('https://api.github.com/repos/'+repo+'/git/trees/'+sha,f)
  if not r or r.get('status')!=200:continue
  root=json.loads((D/'sources'/f).read_text())
  for x in root['tree']:
   if x['path'] in dirs:fetch('https://api.github.com/repos/'+repo+'/git/trees/'+x['sha']+'?recursive=1',repo.replace('/','-')+'-'+x['path']+'.json')
elif mode=='abs':
 for a in sorted(set(x['source_url'].split('/')[-1] for x in json.loads((D/'extracted.json').read_text()).values())):fetch('https://arxiv.org/abs/'+a,'abs-'+a+'.html')
elif mode=='search':
 for q in ['"2607.28616" lean','"Hurlbert" "pebbling" lean','"2506.01315" lean','"Paper Boat" lean','"Miura" lean','"2502.10903" lean','"2506.08858" lean','"2506.14088" lean']:
  r=fetch('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),'github-search-'+str(len(list((D/'sources').glob('github-search-*'))))+'.json')
  if r and r.get('status') in (403,429):break
  time.sleep(7)
