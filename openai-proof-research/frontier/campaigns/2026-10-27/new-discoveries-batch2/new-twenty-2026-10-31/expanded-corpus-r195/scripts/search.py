import pathlib,json,subprocess,urllib.parse,time
D=pathlib.Path(__file__).resolve().parents[1]
x=json.loads((D/'extracted.json').read_text())
for i,v in x.items():
 q='"'+v['source_url'].split('/')[-1]+'" proof conjecture citations'
 subprocess.run(['python3','-I',str(D/'scripts/fetch.py'),i+'-literature','https://www.google.com/search?q='+urllib.parse.quote(q)],check=True)
qs=['"2501.02925" lean','"2502.00799" lean','"2509.11494" lean','"2509.20247" lean','"2503.19696" lean','"2606.29015" lean','"2401.05510" lean','"partition" "Ono" lean']
for j,q in enumerate(qs):
 subprocess.run(['python3','-I',str(D/'scripts/fetch.py'),f'github-search-{j}','https://api.github.com/search/repositories?q='+urllib.parse.quote(q)],check=True)
 r=json.loads((D/f'sources/github-search-{j}.receipt.json').read_text())
 if r.get('status') in (403,429) or r.get('error'):break
 time.sleep(8)
