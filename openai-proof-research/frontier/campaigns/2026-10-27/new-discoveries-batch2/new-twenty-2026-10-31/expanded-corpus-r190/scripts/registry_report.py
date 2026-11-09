import pathlib,json,re,datetime,hashlib
D=pathlib.Path(__file__).resolve().parents[1];rows=json.loads((D/'reservation.json').read_text())['rows'];v=json.loads((D/'outputs/versions.json').read_text());r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'heads':{},'screens':{},'github_searches':[],'limitations':['Eight arXiv-ID-plus-lean repository searches; no code search or exhaustive public proof audit.','Lean Pool projects.yml and all candidates/ blob bodies screened, proof bodies not exhaustively read.','Omega D5/Problems and OpenAI preprints path screens only; path non-matches are not novelty clearance.']}
for n in ['leanpool','omega','openai']:r['heads'][n]=json.loads((D/f'sources/{n}-head.body').read_text()).get('sha')
terms={str(x['mathdb_id']):[str(x['mathdb_id']),v[str(x['mathdb_id'])]['arxiv']]+re.findall(r'[A-Z][a-z]{4,}',x['title']) for x in rows}
terms['334519']+=['Perarnau','occupancy'];terms['373247']+=['Sehrawat','signed complete'];terms['329942']+=['Rolnick','modular p-free'];terms['329603']+=['expanding spheres'];terms['330178']+=['0-sum 3-flow'];terms['334564']+=['bounded representation'];terms['334926']+=['fair representation'];terms['334235']+=['Doryn','semilinear']
for i,ts in terms.items():
 hits=[]
 for p in (D/'sources').glob('pool-file-*.body'):
  for n,l in enumerate(p.read_text().splitlines(),1):
   if any(t.lower() in l.lower() for t in ts):hits.append({'file':str(p.relative_to(D)),'line':n,'text':l[:400]})
 trees=[]
 for name in ['omega-D5','omega-Problems','openai-preprints']:
  x=json.loads((D/f'sources/{name}.body').read_text());matched=[z['path'] for z in x.get('tree',[]) if any(t.lower() in z['path'].lower() for t in ts)]
  trees.append({'name':name,'truncated':x.get('truncated'),'entries':len(x.get('tree',[])),'hits':matched})
 r['screens'][i]={'terms':ts,'leanpool_body_hits':hits,'path_screens':trees,'novelty_cleared':False}
for p in sorted((D/'sources').glob('github-search-*.receipt.json')):
 rec=json.loads(p.read_text());body=p.with_name(p.name.replace('.receipt.json','.body'));x=json.loads(body.read_text()) if body.exists() else {};r['github_searches'].append({'receipt':str(p.relative_to(D)),'url':rec['url'],'status':rec.get('status'),'total_count':x.get('total_count'),'hits':x.get('items',[])})
(D/'outputs/registry-screen.json').write_text(json.dumps(r,indent=2));print('github',len(r['github_searches']),'hits',sum(len(x['hits']) for x in r['github_searches']))
for i,x in r['screens'].items():print(i,'pool hits',len(x['leanpool_body_hits']),'paths',[(z['name'],len(z['hits'])) for z in x['path_screens']])
