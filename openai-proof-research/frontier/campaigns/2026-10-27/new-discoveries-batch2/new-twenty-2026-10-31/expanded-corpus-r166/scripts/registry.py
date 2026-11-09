exec(compile(open('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166/scripts/fetch.py').read().split("if sys.argv[1]")[0], 'fetch.py','exec'))
j=json.loads((D/'sources/lean-pool-tree.json').read_text());sha=json.loads((D/'sources/lean-pool-head.json').read_text())['sha']
paths=[r['path'] for r in j['tree'] if r['path'].endswith('projects.yml') or r['path'].startswith('candidates/') and r['type']=='blob']
print(paths)
for p in paths:fetch(f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/{p}','pool/'+p)
queries=['"Kolokolnikov" lean','"1407.5480" lean','"Markstrom" "homomorphism" lean','"1211.0463" lean','"Kiss" "Vidnyanszky" lean','"Horovitz" "Etzion" lean','"Bronski" "DeVille" lean','"Meroueh" lean']
for i,q in enumerate(queries):
 j=fetch('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),f'github-search-{i+1}.json')
 if j is None:break
 time.sleep(8)
