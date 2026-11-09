import pathlib,json,importlib.util
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
s=importlib.util.spec_from_file_location('fetch',L/'scripts/fetch.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
sha=json.loads((L/'sources/omega-head.json').read_text())['sha']
data=m.fetch(f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{sha}','sources/omega-root-tree.json')
if data:
 for x in json.loads(data)['tree']:
  if x['path'] in ['D5','Problems']:
   m.fetch(f"https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{x['sha']}?recursive=1",f"sources/omega-{x['path']}-tree.json")
