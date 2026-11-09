import sys,pathlib,json,urllib.parse,time
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import fetch,L
h=json.loads((L/'receipts/leanpool-head.body').read_text())['sha'];ps=json.loads((L/'outputs/registry-paths.json').read_text())
for i,p in enumerate(ps):
 if not (L/'receipts'/f'pool-file-{i}.json').exists():fetch(f'https://raw.githubusercontent.com/Vilin97/lean-pool/{h}/{p}',f'pool-file-{i}')
for i,q in enumerate(['"Gottlieb" "king" lean','"van der Pol" "basis" lean','"Kruft" lean','"double Hall" lean'],2):
 fetch('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),f'github-search-{i:02}');time.sleep(8)
 if json.loads((L/'receipts'/f'github-search-{i:02}.json').read_text()).get('status') in [403,429]:break
