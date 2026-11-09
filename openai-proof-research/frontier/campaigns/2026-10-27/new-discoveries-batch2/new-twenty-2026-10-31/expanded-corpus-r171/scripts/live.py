import pathlib,sys,json,time,urllib.parse
exec(compile((pathlib.Path(__file__).parent/'fetch.py').read_text().split("if sys.argv[1]=='sources':")[0],str(pathlib.Path(__file__).parent/'fetch.py'),'exec'))
if sys.argv[1]=='versions':
 urls=sorted(set(o['source_url'] for o in json.loads((D/'extracted.json').read_text()).values()))
 for u in urls:fetch(u,'abs-'+u.rsplit('/',1)[-1]+'.html')
elif sys.argv[1]=='search':
 qs=['"2604.16759" lean','"Inverse" "cross" lean','"2606.11494" lean','"2606.27961" lean','"Braun" "Bruegge" lean','"Dong" "chromatic" lean','"Bona" "avoidance" lean','"2605.21718" lean']
 for q in qs:
  r=fetch('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),'github-search-'+str(qs.index(q))+'.json')
  if r.get('status') in (403,429):break
  time.sleep(8)
