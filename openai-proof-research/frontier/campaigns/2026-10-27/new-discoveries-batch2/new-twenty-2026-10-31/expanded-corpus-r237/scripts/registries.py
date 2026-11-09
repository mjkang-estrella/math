from pathlib import Path
import json,runpy,urllib.parse,time
L=Path(__file__).resolve().parents[1];get=runpy.run_path(str(L/'scripts/http.py'))['get']
sha=json.loads((L/'sources/lean-pool-head.json').read_text())['sha']
get('lean-pool-tree.json',f'https://api.github.com/repos/Vilin97/lean-pool/git/trees/{sha}?recursive=1')
tree=json.loads((L/'sources/lean-pool-tree.json').read_text())['tree']
for o in tree:
 if o['path']=='projects.yml' or o['path'].startswith('candidates/') and o['type']=='blob':
  get('pool-'+o['path'].replace('/','--'),f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/'+o['path'])
for k,r in [('openai','openai/math'),('omega','the-omega-institute/trureturing')]:get(k+'-head.json','https://api.github.com/repos/'+r+'/commits/HEAD')
queries=['"2107.03905" lean','"2109.13637" lean','"2108.10042" lean','"2106.06750" lean','"eventown" lean','"Franke" "Muthiah" lean']
for j,q in enumerate(queries):
 r=get(f'github-search-{j}.json','https://api.github.com/search/repositories?q='+urllib.parse.quote(q))
 if r.get('status') in (403,429) or r.get('error'):break
 time.sleep(8)
