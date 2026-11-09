import pathlib,json,importlib.util,urllib.parse,time
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
s=importlib.util.spec_from_file_location('fetch',L/'scripts/fetch.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
sha=json.loads((L/'sources/leanpool-head.json').read_text())['sha']
m.fetch(f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/LeanPool/projects.yml','sources/leanpool-projects.yml')
qs=['"Steiner" "radius" lean','"2511.22492" lean','"total cut" lean','"2602.21427" lean','"flow reconfiguration" lean','"Kanungo" lean','"tropical" "dot product" lean','"spectral" "chromatic" lean']
out=[]
for j,q in enumerate(qs):
 if j:time.sleep(8)
 data=m.fetch('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),f'sources/github-search-{j}.json')
 out.append(dict(query=q,path=f'sources/github-search-{j}.json',data=json.loads(data) if data else None))
 if not data:break
(L/'outputs/github-queries.json').write_text(json.dumps(out,indent=2))
