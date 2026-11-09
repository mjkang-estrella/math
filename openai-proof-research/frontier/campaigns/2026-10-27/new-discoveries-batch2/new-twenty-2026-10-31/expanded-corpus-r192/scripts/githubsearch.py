import pathlib,runpy,sys,urllib.parse,time
D=pathlib.Path(__file__).resolve().parents[1]
qs=['"1412.6473" lean','"1409.8108" lean','"1611.05482" lean','"1404.3876" lean','"1409.2192" lean','"1411.3674" lean','"Horak Rosa" lean','"Bollobas Scott" lean']
for n,q in enumerate(qs):
 if any('"status": 403' in p.read_text() or '"status": 429' in p.read_text() for p in (D/'sources').glob('github-search-*.receipt.json')):break
 sys.argv=[str(D/'scripts/fetch.py'),'github-search-'+str(n),'https://api.github.com/search/repositories?q='+urllib.parse.quote(q)];runpy.run_path(sys.argv[0],run_name='__main__');time.sleep(8)
