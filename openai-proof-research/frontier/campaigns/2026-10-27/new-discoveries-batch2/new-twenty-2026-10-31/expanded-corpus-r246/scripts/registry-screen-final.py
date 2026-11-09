import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];rs=json.loads((D/'extracted.json').read_text());patterns=[r'(?<!\d)'+i+r'(?!\d)' for i in rs]+[re.escape(x['source_url'].split('/')[-1]) for x in rs.values()]+[r'\bantimagic\b',r'\bLau\b',r'\bShiu\b',r'\bM[oö]bius\s+ladder',r'\bmulticone\b',r'\bacyclic.{0,12}matching\b',r'\bneighbor.locating\b',r'\bSeifert.{0,12}(cycle|Gauss)']
p=re.compile('|'.join(patterns),re.I);hits=[]
for f in (D/'sources').glob('leanpool-candidates*'):
 if f.name.endswith('.receipt.json'):continue
 for n,line in enumerate(f.read_text().splitlines(),1):
  if p.search(line):hits.append({'file':f.name,'line':n,'text':line[:2000]})
(D/'outputs').mkdir(exist_ok=True)
o={'heads':{name:json.loads((D/f'sources/{name}-head.json').read_text())['sha'] for name in ['openai','leanpool','omega']},'lean_pool_raw_index_files':[x[0] for x in json.loads((D/'queue-pool-full.json').read_text())],'lean_pool_index_hits':hits,'projects_yml':'404 retained, no retry; not present in complete tree','github_repository_search':json.loads((D/'repo-search-results.json').read_text()),'timing_caveat':'Live tree/path and web screens preceded numerical work. Mandatory raw candidate-index fetch/grep and unauthenticated repository-API queries were added during final audit, after the witness and Lean certificate. This sequencing failure is disclosed; no claim of fully compliant pre-investment clearance. Candidate remains on hold.','limits':'Raw candidates index scan and tree names are not a full scan of all proof repository bodies; OpenAI/Omega recursive trees truncated.'}
(D/'outputs/registry-screen.json').write_text(json.dumps(o,indent=2));print('index hits',len(hits));print('repos',o['github_repository_search'])
