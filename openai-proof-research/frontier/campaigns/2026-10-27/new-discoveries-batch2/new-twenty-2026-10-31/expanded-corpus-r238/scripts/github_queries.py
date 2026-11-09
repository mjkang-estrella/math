import pathlib,importlib.util,urllib.parse,time,json
D=pathlib.Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('h',D/'scripts/http.py');h=importlib.util.module_from_spec(s);s.loader.exec_module(h)
queries=['"2111.03877" lean','"high-ordered" lean','"345516" lean','"polygon intersections" lean','"Gao" "principal specialization" lean','"2002.09570" lean']
for i,q in enumerate(queries):
 r=h.get(f'github-target-{i}.json','https://api.github.com/search/repositories?q='+urllib.parse.quote(q))
 if r.get('status') in (403,429):break
 time.sleep(8)
