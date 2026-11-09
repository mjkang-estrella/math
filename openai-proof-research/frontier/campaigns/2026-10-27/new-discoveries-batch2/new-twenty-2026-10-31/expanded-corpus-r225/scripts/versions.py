import pathlib,re,importlib.util,json
D=pathlib.Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('fetch',D/'scripts/fetch.py');f=importlib.util.module_from_spec(s);s.loader.exec_module(f)
for p in sorted((D/'sources').glob('*-abs.html')):
 a=p.name.split('-abs')[0];vs=sorted(set(re.findall(r'/abs/'+re.escape(a)+r'v(\d+)',p.read_text())))
 for v in vs:print(f.get(a+'v'+v+'.html','https://arxiv.org/html/'+a+'v'+v),flush=True)
