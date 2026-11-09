import pathlib,json,runpy
D=pathlib.Path(__file__).resolve().parents[1];get=runpy.run_path(str(D/'scripts/fetch.py'))['get']
for a,vs in json.loads((D/'versions.json').read_text()).items():
 a=a.removesuffix('-abs')
 for v in vs[:-1]:get(a+'v'+v+'.html','https://arxiv.org/html/'+a+'v'+v)
get('openai-preprints.json','https://api.github.com/repos/openai/math/git/trees/3f56f68a176b4494c346091ea0a319651bc217ec?recursive=1')
x=json.loads((D/'sources/omega-root.json').read_text());print([(a['path'],a['sha']) for a in x['tree'] if a['type']=='tree'])
