import pathlib,json,importlib.util,time,urllib.parse
D=pathlib.Path(__file__).resolve().parents[1];sp=importlib.util.spec_from_file_location('lh',D/'scripts/http.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
queries=['"coset factorization" lean','braiding tree lean','pagenumber lean','Kuhl McGinn lean','"Stern poset" lean','"rainbow matching" lean','quiddity lean','"gain-graphic" lean']
rows=[]
for i,q in enumerate(queries):
 r=h.get('github-query-'+str(i)+'.json','https://api.github.com/search/repositories?q='+urllib.parse.quote(q));rows.append({'query':q,'receipt':r})
 if r.get('status') in (403,429) or 'error' in r:break
 time.sleep(2)
terms=[str(i) for i in json.loads((D/'reservation.json').read_text())['ids']]+[x['source_url'].rsplit('/',1)[-1] for x in json.loads((D/'extracted.json').read_text()).values()]+['Zhao','Levin','Ramos','Young','Shao','Ren','Gittins','Helffer','Kennedy','Pierro','Aharoni','Chang','Roussel','Jaume','Pastine','Schvollner','Macajova','Mazzuoccolo','Mkrtchyan','Zerafa','Glazyrin','Funk','Mayhew','Ghorbani','Kuhl','McGinn','Casselgren','Goransson','Kazhdan','Ziegler','Stern','Mabilat','Stoica']
hits={}
for p in (D/'sources').glob('lean-pool-*'):
 if p.name.endswith('.json'):continue
 hits[p.name]=[{'line':i+1,'text':l,'terms':[t for t in terms if t.lower() in l.lower()]} for i,l in enumerate(p.read_text(errors='replace').splitlines()) if any(t.lower() in l.lower() for t in terms)]
(D/'outputs').mkdir(exist_ok=True)
(D/'outputs/registry-screen.json').write_text(json.dumps({'path_and_keyword_screen':'../registry-screen.json','queries':rows,'lean_pool_full_term_hits':hits,'chronology_limit':'Live heads, trees and initial GitHub web search preceded heavy searches. Direct repository API queries and expanded author/ID grep were completed later; no candidate advanced.'},indent=2)+'\n')
