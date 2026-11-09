import sys,json,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch_http import get
D=pathlib.Path(__file__).resolve().parents[1]
for key,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 sha=json.loads((D/f'http/{key}-head.json').read_text())['sha'];get(key+'-root.json',f'https://api.github.com/repos/{repo}/git/trees/{sha}')
 root=json.loads((D/f'http/{key}-root.json').read_text())
 for p in (['Problems'] if key=='omega' else ['preprints']):
  e=next((e for e in root['tree'] if e['path']==p),None)
  if e:get(key+'-'+p+'-complete.json',f'https://api.github.com/repos/{repo}/git/trees/{e["sha"]}?recursive=1')
 if key=='openai':
  for p in ['lean/docs/013.md','preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.tex']:get(key+'-'+p.replace('/','-'),f'https://raw.githubusercontent.com/{repo}/{sha}/{p}')
get('2503.01665.html','https://arxiv.org/html/2503.01665')
