import pathlib,json,sys,urllib.parse
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import fetch,L
h=json.loads((L/'receipts/leanpool-head.body').read_text())['sha']
fetch(f'https://raw.githubusercontent.com/Vilin97/lean-pool/{h}/projects.yml','leanpool-projects')
fetch(f'https://api.github.com/repos/Vilin97/lean-pool/git/trees/{h}?recursive=1','leanpool-tree')
for name,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math')]:fetch(f'https://api.github.com/repos/{repo}/commits/HEAD',name+'-head')
q='"2501.14640" lean OR "2502.03673" lean OR "terminal set" lean'
fetch('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),'github-search-01')
