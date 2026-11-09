import pathlib,subprocess,urllib.parse,time,json
D=pathlib.Path(__file__).resolve().parents[1]
qs=['"maximal chains" lean','"replication" "Szykula" lean','"Gowravaram" lean','"1201.3299" lean','"signed path" lean','"Nase" lean','"strict gammoids" lean','"rigidity" "Jordan" lean']
for j,q in enumerate(qs):
 p=subprocess.run(['python3','-I',str(D/'scripts/fetch.py'),f'github-search-{j}', 'https://api.github.com/search/repositories?q='+urllib.parse.quote(q)],check=True)
 r=json.loads((D/f'sources/github-search-{j}.receipt.json').read_text())
 if r.get('status') in (403,429) or r.get('error'):break
 time.sleep(8)
