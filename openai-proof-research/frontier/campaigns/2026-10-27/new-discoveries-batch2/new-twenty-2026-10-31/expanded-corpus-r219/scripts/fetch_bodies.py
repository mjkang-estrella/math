import sys,json,pathlib,re
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch_http import get
D=pathlib.Path(__file__).resolve().parents[1]
for repo,key in [('Vilin97/lean-pool','leanpool'),('openai/math','openai'),('the-omega-institute/trureturing','omega')]:
 sha=json.loads((D/f'http/{key}-head.json').read_text())['sha'];get(key+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1')
 if key=='leanpool':get('leanpool-projects.yml',f'https://raw.githubusercontent.com/{repo}/{sha}/projects.yml')
for p in sorted((D/'http').glob('*-abs.html')):
 aid=p.name.split('-abs')[0];s=p.read_text();vs=sorted(set(re.findall(r'\['+r'v(\d+)\]',s))) or ['1']
 print(aid,'versions',vs,flush=True)
 for v in vs:get(aid+'v'+v+'.html',f'https://arxiv.org/html/{aid}v{v}')
