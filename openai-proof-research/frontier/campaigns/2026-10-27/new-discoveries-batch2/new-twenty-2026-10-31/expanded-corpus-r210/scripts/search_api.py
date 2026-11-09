from pathlib import Path
import importlib.util,json,urllib.parse,time
L=Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('fetch',L/'scripts/fetch.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
queries=['"1902.04055" lean','"2604.12557" lean','"Sundaram" "positivity" lean','"1810.07856" lean','"Wormald" lean','"Hepp" lean','"Schmidt" "binary" lean','"1806.06821" lean']
rows=[]
for q in queries:
 b=m.fetch('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),'repo-search-'+str(len(rows)))
 if not b:break
 d=json.loads(b);rows.append({'query':q,'total_count':d.get('total_count'),'hits':[x['full_name'] for x in d.get('items',[])]});time.sleep(8)
(L/'outputs/github-search.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows))
