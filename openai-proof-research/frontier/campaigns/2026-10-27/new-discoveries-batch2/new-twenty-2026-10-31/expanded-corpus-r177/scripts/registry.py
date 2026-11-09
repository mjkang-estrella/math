import pathlib,json,re,sys,time,urllib.parse
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'scripts'));from fetch import get
queries=['"pinnacle" "lean"','"Gessel" "Zhuang" "lean"','"Brimkov" "lean"','"2307.09663" "lean"','"Crupi" "Ficarra" "lean"','"frustrated" "lean"','"off-diagonal" "common" "lean"','"Morita" "graph" "lean"']
results=[]
for j,q in enumerate(queries):
 rec=get('github-search-'+str(j)+'.json','https://api.github.com/search/repositories?q='+urllib.parse.quote(q));results.append({'query':q,**rec})
 if 'error' in rec:break
 time.sleep(8)
x=json.loads((D/'extracted.json').read_text());matches={}
for i,o in x.items():
 terms=[i,o['source_url'].rsplit('/',1)[-1]]
 matches[i]=[]
 for p in [D/'sources/projects.yml',*list((D/'sources').glob('pool-*'))]:
  for n,l in enumerate(p.read_text(errors='replace').splitlines(),1):
   if any(t.lower() in l.lower() for t in terms):matches[i].append({'path':str(p.relative_to(D)),'line':n,'text':l})
r={'heads':{k:json.loads((D/'sources'/f'{k}-head.json').read_text())['sha'] for k in ['leanpool','openai','omega']},'github_queries':results,'exact_id_and_arxiv_matches':matches,'scope':'Lean Pool projects.yml and all ten candidates files; repository search is bounded, no global proof clearance'}
(D/'outputs/registry-screen.json').write_text(json.dumps(r,indent=2))
