import pathlib,json,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'outputs/registry-screen.json').read_text());r['github_queries']=[]
for p in sorted((D/'sources').glob('github-search-*.json')):
 if p.name.endswith('receipt.json'):continue
 receipt=json.loads(p.with_suffix('.json.receipt.json').read_text());body=json.loads(p.read_text());r['github_queries'].append({'receipt':receipt,'total_count':body.get('total_count'),'items':[{k:o.get(k) for k in ['full_name','description','html_url']} for o in body.get('items',[])]})
r['complete_scopes']={}
for p in (D/'sources').glob('*-complete.json'):
 t=json.loads(p.read_text());r['complete_scopes'][p.name]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'truncated':t.get('truncated'),'entries':len(t['tree']),'path_hits_file':f'outputs/{p.stem}-hits.json'}
r['interpretation']={'numeric_substrings_in_sha_are_not_hits':True,'pool_relevant_hit':'Common-neighbour-conjecture: prior Saxl counterexample; catalogue actual text inspected','omega_root_and_openai_root_truncated':'Do not use negative root-tree greps as complete screens; complete D5/Problems and preprints scopes fetched separately','openai_Saxl_name_collision':'ComparatorChallenges/Saxl concerns representation theoretic Saxl conjecture; not the Burness-Giudici target','remaining_limits':['No all-proof-body audit','No deleted-history audit','GitHub repository queries do not search every file','No universal novelty clearance']}
(D/'outputs/registry-screen.json').write_text(json.dumps(r,indent=2)+'\n')
