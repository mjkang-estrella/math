import runpy,pathlib,urllib.parse,json,time
D=pathlib.Path(__file__).resolve().parents[1];f=runpy.run_path(str(D/'scripts/fetch.py'))['fetch']
queries=['"2510.01110" lean','"2510.18265" lean','"2510.06651" lean','"2506.18788" lean','"2508.02985" lean','"2510.11724" lean','"2509.17705" lean','"equitable matroid" lean']
for i,q in enumerate(queries):
 b=f('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),f'sources/github-search-{i}.json')
 if b is None:break
 time.sleep(8)
