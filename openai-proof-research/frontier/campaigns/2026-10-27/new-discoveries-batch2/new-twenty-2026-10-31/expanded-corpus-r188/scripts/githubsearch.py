import pathlib,urllib.parse,subprocess,sys,time
D=pathlib.Path(__file__).resolve().parents[1]
qs=['"1707.03928" lean','"signed shifts" lean','"cordial" "hypertrees" lean','"Reitzner" "covariance" lean','"Galashin" "R-systems" lean','"pseudocircle" lean']
for n,q in enumerate(qs):
 if n:time.sleep(8)
 subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),'github-search-'+str(n),'https://api.github.com/search/repositories?q='+urllib.parse.quote(q)],check=True)
 import json
 r=json.loads((D/f'sources/github-search-{n}.receipt.json').read_text())
 if r.get('status') in (403,429):break
