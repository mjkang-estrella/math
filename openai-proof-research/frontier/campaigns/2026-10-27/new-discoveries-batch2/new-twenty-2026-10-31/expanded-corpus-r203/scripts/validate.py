import sys,pathlib,itertools,json,hashlib,re
D=pathlib.Path(sys.argv[1]);s=(D/'scripts/lattice.py').read_text();exec(s[s.index('def clique'):s.index('for m in [7,8]:')])
for h in range(1<<10):
 a=[0]*5
 for j,(u,v) in enumerate(itertools.combinations(range(5),2)):
  if h>>j&1:a[u]|=1<<v;a[v]|=1<<u
 brute=max(I.bit_count() for I in range(32) if all((a[u]&I)==(I^(1<<u)) for u in range(5) if I>>u&1))
 assert len(clique(a))==brute
print('Clique checker agrees with brute force on all 1024 labelled graphs of order 5.')
R=json.loads((D/'results.json').read_text());res=json.loads((D/'reservation.json').read_text());assert set(R)==set(map(str,res['ids']))
for i,r in R.items():
 b=(D/'raw'/f'{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==r['provenance']['raw_sha256']
 assert hashlib.sha256(r['statement'].encode()).hexdigest()==r['provenance']['statement_utf8_sha256']
print('Exactly 20 reserved keys; raw and statement hashes agree.')
registry=json.loads((D/'outputs/registry-screen.json').read_text());registry['complete_scope_path_screens']=[]
terms=['Parry','Attractor','LaplacianRatio','Kashima','FriendsAndStrangers','MatchingTrace','DominatedNumber','SaturationClique','BaoYu','DistanceSets','UnitGraph','Steklov','BraidArrangement']
for label in ['omega-d5','omega-Problems-complete','openai-preprints-complete']:
 p=D/'sources'/label/'body';o=json.loads(p.read_text());hits=[x['path'] for x in o['tree'] if any(t.lower() in x['path'].lower() for t in terms)]
 registry['complete_scope_path_screens'].append({'snapshot':str(p.relative_to(D)),'truncated':o.get('truncated'),'entries':len(o['tree']),'terms':terms,'path_hits':hits})
registry['limitations']='Root recursive trees truncated; separate D5, Problems and preprints scopes fetched. Actual truncation flags recorded. These are path screens, not a proof-body audit; no global novelty clearance.'
(D/'outputs/registry-screen.json').write_text(json.dumps(registry,indent=2))
print(json.dumps(registry['complete_scope_path_screens'],indent=2))
