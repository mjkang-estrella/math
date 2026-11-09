import pathlib,json,importlib.util,time,urllib.parse,re
D=pathlib.Path(__file__).resolve().parents[1];sp=importlib.util.spec_from_file_location('h',D/'scripts/http.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
r={}
for key,repo in [('pool','Vilin97/lean-pool'),('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 sha=json.loads((D/'sources'/f'{key}-head/body').read_text())['sha'];r[key]={'head':sha};h.get(key+'-tree','https://api.github.com/repos/'+repo+'/git/trees/'+sha+'?recursive=1')
 if key=='pool':
  tree=json.loads((D/'sources/pool-tree/body').read_text());paths=[x['path'] for x in tree['tree'] if x['type']=='blob' and (x['path']=='projects.yml' or x['path'].startswith('candidates/'))]
  r[key]['paths']=paths
  for i,p in enumerate(paths):h.get('pool-file-'+str(i),'https://raw.githubusercontent.com/'+repo+'/'+sha+'/'+p)
queries=['"determinantal" lean','"Seacrest" lean','"numerical semigroups" lean','"inducibility" lean','"Yancey" lean','"Kriesell" lean','"1704.04964" lean','"Z-polynomial" lean']
r['github_queries']=[]
for i,q in enumerate(queries):
 if i:time.sleep(9)
 rec=h.get('github-query-'+str(i),'https://api.github.com/search/repositories?q='+urllib.parse.quote(q));r['github_queries'].append({'query':q,'receipt':rec})
 if rec.get('status') in (403,429):break
terms=[str(i) for i in json.loads((D/'reservation.json').read_text())['ids']]+['determinantal','Seacrest','Eliahou','Fromentin','inducibility','Yancey','Kriesell','Eger','Wronskian','Alishahi','Meunier','Hibi','Ohsugi','Bang-Jensen','Tetali','1705.09725','1811.11235','1704.04964']
r['path_or_text_hits']={}
for p in (D/'sources').glob('pool-file-*/body'):
 t=p.read_text(errors='replace');hits=[s for s in terms if s.lower() in t.lower()]
 if hits:r['path_or_text_hits'][str(p)]=hits
for k in ['omega','openai']:
 p=D/'sources'/f'{k}-tree/body';data=json.loads(p.read_text());r[k]['truncated']=data.get('truncated');r[k]['path_hits']=[x['path'] for x in data.get('tree',[]) if any(s.lower() in x['path'].lower() for s in terms)]
r['limitation']='Path/registry text screen only; not an exhaustive proof implication audit. Search queries capped at 8 and spaced 9 seconds.'
(D/'outputs/registry-screen.json').write_text(json.dumps(r,indent=2))
