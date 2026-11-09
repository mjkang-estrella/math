import pathlib,re,json,sys,importlib.util
D=pathlib.Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('fetch',D/'scripts/fetch.py');f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
out={}
for p in sorted((D/'sources').glob('*.abs.html')):
 a=p.name.removesuffix('.abs.html');s=p.read_text();vs=sorted(set(re.findall(r'/abs/'+re.escape(a)+r'v(\d+)',s)),key=int)
 vs=list(range(1,max(map(int,vs),default=1)+1));out[a]=vs
(D/'outputs/versions.json').write_text(json.dumps(out,indent=2)+'\n')
for a,vs in list(out.items())[int(sys.argv[1]):int(sys.argv[2])]:
 for v in vs:f.get(a+'v'+str(v)+'.pdf','https://arxiv.org/pdf/'+a+'v'+str(v))
print(out)
