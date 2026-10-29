exec((__import__('pathlib').Path(__file__).parent/'read.py').read_text().split('for name,url in')[0])
h=json.loads(get('omega-HEAD.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'));head=h['sha'];print('HEAD',head,h['commit']['committer'],flush=True)
d=json.loads(get('omega-HEAD-delta.json',f'https://api.github.com/repos/the-omega-institute/trureturing/compare/73a5033dd654a16a14fcd1b13277f1a03d81d826...{head}'));print('DELTA',d.get('total_commits'),len(d.get('files',[])),flush=True)
for i,f in enumerate(d.get('files',[])):
 if f['status']!='removed':get(f'current-delta-{i}.txt',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/'+f['filename'])
b=get('omega-HEAD-tree.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{head}?recursive=1');t=json.loads(b);terms=re.compile(r'mesh|boxed|Bruhat|Heilbronn|Kitaev|Sudermann|2143',re.I);hits=[x['path'] for x in t.get('tree',[]) if terms.search(x['path'])];print('TREE',t.get('truncated'),len(t.get('tree',[])),hits,flush=True)
for i,p in enumerate(hits):
 if p.endswith(('.lean','.md','.tex')):get(f'current-body-{i}.txt',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/'+p)
get('original-author.pdf','https://personal.strath.ac.uk/sergey.kitaev/Papers/mesh.pdf')
get('openai-HEAD.json','https://api.github.com/repos/openai/math/commits/HEAD')
R=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');audit=[];matches=[];terms=re.compile(r'boxed.mesh|2609.13764|Bruhat.*degree|degree.*Bruhat|strict.interleav|Heilbronn|Sudermann|critical.triangles',re.I)
for p in R.rglob('*'):
 if not p.is_file() or L in p.parents:continue
 if not (p.name.lower() in ['summary.md','discovery.md','findings.md','proof.md','ledger.json','next.md'] or 'review' in str(p.relative_to(R)).lower() and p.suffix in ['.md','.json','.txt']):continue
 b=p.read_bytes();audit.append({'path':str(p.relative_to(R)),'sha256':hashlib.sha256(b).hexdigest()});ls=[s for s in b.decode(errors='replace').splitlines() if terms.search(s)]
 if ls:matches.append({'path':str(p.relative_to(R)),'lines':ls[:25]})
(L/'duplicate-expanded.json').write_text(json.dumps({'terms':terms.pattern,'files':audit,'hits':matches},indent=2));print('AUDIT',len(audit),json.dumps(matches)[:13000],flush=True)
