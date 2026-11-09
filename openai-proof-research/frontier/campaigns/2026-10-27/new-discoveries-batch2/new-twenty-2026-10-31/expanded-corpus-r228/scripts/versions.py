import pathlib,json,runpy
D=pathlib.Path(__file__).resolve().parents[1];get=runpy.run_path(str(D/'scripts/fetch.py'))['get']
for a in dict.fromkeys(x['source_url'].rsplit('/',1)[-1] for x in json.loads((D/'extracted.json').read_text()).values()):get(a+'-abs.html','https://arxiv.org/abs/'+a)
