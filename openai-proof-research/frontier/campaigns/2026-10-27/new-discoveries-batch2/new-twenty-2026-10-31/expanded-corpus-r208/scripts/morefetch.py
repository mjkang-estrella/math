import pathlib,json,importlib.util,urllib.parse
D=pathlib.Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('h',D/'scripts/http.py');h=importlib.util.module_from_spec(s);s.loader.exec_module(h)
req=[('leanpool-projects-current.yml','https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/projects.yml'),('omega-root.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/a8f1af6c2a2679392be1d3fb660bd114452b1370')]
for a in ['2202.13548v1','2301.05202v1','2305.10711v1','2308.13887v1','2407.19157v1','2408.07863v1','2410.23009v1','2411.13818v1','2411.13818v2','2411.14308v1','2411.14308v2','2509.13097','2605.22808','2412.13485','2504.05510','2504.17387']:
 req.append((a+'-version.html','https://arxiv.org/html/'+a))
req.extend([('prior-inversion.html','https://probxiv.com/problems/cyclic-sieving-on-permutations-an-analysis-of-maps-and-statistics-in'),('prior-pgst.html','https://www.trureturing.org/research/bhattacharjya-monterde-pal-2024-double-blow-up-pgst/')])
for k,u in req:h.get(k,u)
