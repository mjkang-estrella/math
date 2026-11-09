import pathlib,sys,re,json
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
out=json.loads((D/'outputs/registry-screen.json').read_text());rows=json.loads((D/'extracted.json').read_text());terms={i:[i,o['source_url'].rsplit('/',1)[-1]] for i,o in rows.items()}
extra={'346718':['Feiling','interlacing'],'341850':['Brakensiek','submodular separation'],'344469':['Tenner','Glaisher'],'346681':['Kreweras','Rubey'],'340017':['Sundaram','Schur positivity'],'348219':['small doubling','Lev'],'348578':['fullerene'],'348041':['synchronisation','Dey'],'340613':['ballot','Spiro']}
for i,t in extra.items():terms[i]+=t
pool=[]
for z in out['receipts']:
 if 'raw.githubusercontent' in z['url'] and z['status']==200:
  s=pathlib.Path(z['body']).read_text()
  for i,ts in terms.items():
   hits=[t for t in ts if t.lower() in s.lower()]
   if hits:pool.append({'id':i,'terms':hits,'receipt_body':z['body']})
out['pool_keyword_hits']=pool;out['github_query_results']=[{'query':z['query'],'status':z['receipt']['status'],'total_count':json.loads(pathlib.Path(z['receipt']['body']).read_text()).get('total_count') if z['receipt']['status']==200 else None,'items':[{'name':a['full_name'],'url':a['html_url']} for a in json.loads(pathlib.Path(z['receipt']['body']).read_text()).get('items',[])]} for z in out['queries']]
for repo in ['openai/math','the-omega-institute/trureturing']:
 sha=out['heads'][repo];z=fetch(f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1','tree-'+repo.split('/')[0]);out['receipts'].append(z)
 if z['status']==200:
  obj=json.loads(pathlib.Path(z['body']).read_text());paths=[a['path'] for a in obj['tree']];out[repo+'-scope']={'truncated':obj.get('truncated'), 'paths':len(paths),'keyword_hits':{i:[p for p in paths if any(t.lower() in p.lower() for t in ts)] for i,ts in terms.items()}}
out['limitations']='Path/metadata screen is not proof-body review; common names such as Lev and Dey generate noise. Eight GitHub queries, spaced seven seconds; no further search queries authorized in this lane.'
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps({'pool':pool,'github':out['github_query_results'],'scopes':{k:v for k,v in out.items() if k.endswith('-scope')}},indent=2))
