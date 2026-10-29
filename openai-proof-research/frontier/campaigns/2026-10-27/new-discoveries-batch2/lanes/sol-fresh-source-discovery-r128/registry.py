from research import *
from concurrent.futures import ThreadPoolExecutor
jobs=[('https://api.github.com/repos/the-omega-institute/trureturing/commits/dev','sources/omega-head.json'),('https://api.github.com/repos/openai/math/commits/main','sources/openai-head.json')]
with ThreadPoolExecutor(max_workers=2) as e:list(e.map(lambda x:fetch(*x),jobs))
p=H/'sources/omega-head.json'
if p.exists():
 x=json.loads(p.read_text());sha=x.get('sha');print('Omega',sha)
 if sha and sha!='9a026fe5527cacf8d3aed5f9291f08bc520ea90b':fetch('https://api.github.com/repos/the-omega-institute/trureturing/compare/9a026fe5527cacf8d3aed5f9291f08bc520ea90b...'+sha,'sources/omega-delta.json')
