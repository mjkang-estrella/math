import sys,pathlib,json,importlib.util,urllib.parse,time
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
spec=importlib.util.spec_from_file_location('fetch',L/'scripts/fetch.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
sha=json.loads((L/'sources/leanpool-head.json').read_text())['sha']
m.fetch(f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/projects.yml','sources/leanpool-projects.yml')
d=m.fetch(f'https://api.github.com/repos/Vilin97/lean-pool/git/trees/{sha}?recursive=1','sources/leanpool-tree.json')
if d:
 for x in json.loads(d)['tree']:
  if x['type']=='blob' and x['path'].startswith('candidates/'):
   dest='sources/pool-'+x['path'].replace('/','_')
   m.fetch(f"https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/{x['path']}",dest)
for repo,name in [('openai/math','openai'),('the-omega-institute/trureturing','omega')]:
 m.fetch(f'https://api.github.com/repos/{repo}/commits/HEAD',f'sources/{name}-head.json')
