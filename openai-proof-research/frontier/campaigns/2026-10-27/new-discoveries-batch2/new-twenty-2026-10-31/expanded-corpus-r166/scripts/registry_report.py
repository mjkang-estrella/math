import pathlib,json,re,hashlib,datetime
D=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166');rows=json.loads((D/'reservation.json').read_text())['rows'];terms=[str(x['mathdb_id']) for x in rows]+[x['source_url'].rsplit('/',1)[1] for x in rows]+['Kolokolnikov','Horovitz','Etzion','Bronski','DeVille','Markström','Markstrom','Méroueh','Meroueh','Vidnyánszky','Rubio-Montiel','Seamone','Stevens','Jonsson','Marberg','Broersma','Shephard','clique-stable','Beer index','full-rank coding']
heads={};screens={}
for key in ['lean-pool','omega','openai']:
 h=json.loads((D/f'sources/{key}-head.json').read_text());t=json.loads((D/f'sources/{key}-tree.json').read_text());heads[key]={'sha':h['sha'],'url':h['url'],'commit_date':h['commit']['committer']['date']};hits=[]
 for e in t.get('tree',[]):
  matched=[s for s in terms if s.lower() in e['path'].lower()]
  if matched:hits.append({'path':e['path'],'terms':matched})
 screens[key]={'type':'path string screen only','truncated':t.get('truncated'),'entries':len(t.get('tree',[])),'hits':hits}
ph=[]
for p in (D/'sources/pool').rglob('*'):
 if not p.is_file():continue
 lines=p.read_text(errors='replace').splitlines();hits=[]
 for i,l in enumerate(lines,1):
  matched=[s for s in terms if s.lower() in l.lower()]
  if matched:hits.append({'line':i,'terms':matched,'text':l[:500]})
 ph.append({'file':str(p.relative_to(D)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'hits':hits})
qs=[]
for i,q in enumerate(['"Kolokolnikov" lean','"1407.5480" lean','"Markstrom" "homomorphism" lean','"1211.0463" lean','"Kiss" "Vidnyanszky" lean','"Horovitz" "Etzion" lean','"Bronski" "DeVille" lean','"Meroueh" lean'],1):
 p=D/f'sources/github-search-{i}.json';j=json.loads(p.read_text());qs.append({'query':q,'total_count':j.get('total_count'),'hits':[{'repo':x['full_name'],'url':x['html_url'],'description':x.get('description')} for x in j.get('items',[])],'receipt_file':str(p.relative_to(D))})
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'heads':heads,'path_screens':screens,'pool_content_screens':ph,'github_repository_queries':qs,'query_spacing_seconds':8,'http_receipts':'outputs/http.jsonl','prior_Lean_exclusion':{'mathdb_id':329493,'repo':'https://github.com/MerLeanProver/ACMaxConjecture','pool_entry':'acmax-conjecture','declaration':'ACMax.acmax_conjecture','body_read':'sources/pool/LeanPool/ACMax.lean','scope':'all n >= 4 exactly 2(n-2) edges','independent_replay':False},'limits':['String/path screening is not a semantic audit of all repository proofs.','Root projects.yml returned 404; tree located LeanPool/projects.yml, which was fetched at the pinned HEAD. No denied-route retry.','Eight spaced unauthenticated GitHub repository searches, no code-search completeness claim.','No global novelty clearance; no credit claimed.']}
(D/'outputs/registry-screen.json').write_text(json.dumps(r,indent=2));print(json.dumps({'heads':heads,'trees':{k:{'entries':v['entries'],'truncated':v['truncated'],'hits':len(v['hits'])} for k,v in screens.items()},'pool_files':len(ph)},indent=2))
