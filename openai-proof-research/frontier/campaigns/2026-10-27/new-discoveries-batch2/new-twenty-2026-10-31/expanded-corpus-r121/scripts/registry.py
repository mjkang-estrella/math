import pathlib,runpy,json,re
D=pathlib.Path(__file__).resolve().parents[1];get=runpy.run_path(str(D/'scripts/fetch.py'))['get'];h=json.loads((D/'sources/omega-head.json').read_text())['sha']
print(get(('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{h}')))
r=json.loads((D/'sources/omega-root.json').read_text())
for x in r['tree']:
 if x['path'] in ['D5','Problems']:print(get(('omega-'+x['path']+'.json',x['url']+'?recursive=1')))
print(get(('2610.06899.html','https://arxiv.org/html/2610.06899')))
