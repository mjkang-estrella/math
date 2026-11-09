import pathlib,runpy,sys,urllib.parse,time
D=pathlib.Path(__file__).resolve().parents[1]
qs=['"1611.01474" lean','"1612.07652" lean','"2602.18244" lean','"1502.06013" lean','"1501.01391" lean','"1610.00668" lean','"1611.03196" lean','"1503.07131" lean']
for n in range(int(sys.argv[1]),int(sys.argv[2])):
 if list((D/'sources').glob('github-search-*.receipt.json')):
  if any('"status": 403' in p.read_text() or '"status": 429' in p.read_text() for p in (D/'sources').glob('github-search-*.receipt.json')):break
 sys.argv=[str(D/'scripts/fetch.py'),'github-search-'+str(n),'https://api.github.com/search/repositories?q='+urllib.parse.quote(qs[n])]
 runpy.run_path(str(D/'scripts/fetch.py'),run_name='__main__');time.sleep(8)
