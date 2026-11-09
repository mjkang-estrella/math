import json,pathlib,itertools,hashlib
D=pathlib.Path(__file__).resolve().parents[1];w=json.loads((D/'outputs/simplicial-structured-witness.json').read_text());edges=set().union(*(set(itertools.combinations(f,2)) for f in w['facets'][:8]));print('missing edges',sorted(set(itertools.combinations(range(8),2))-edges))
colors=json.loads((D/'outputs/colors.json').read_text());rs=colors['rows'];print('color rows',len(rs),'graphs',len({(r['n'],r['trial']) for r in rs}),'lower checks',sum(r['lower_applicable'] for r in rs),'upper checks',sum(r['upper_applicable'] for r in rs),'violations',sum(r['lower_violated'] or r['upper_violated'] for r in rs))
h=json.loads((D/'outputs/htriangle-completed-extension.json').read_text());print('H counts',[(n,m,sum(r['n']==n and r['m']==m for r in h)) for n in [6,7] for m in range(1,6)])
R=json.loads((D/'results.json').read_text());assert len(R)==20
for i,o in R.items():
 assert hashlib.sha256((D/'raw'/f'{i}.jsonl').read_bytes()).hexdigest()==o['provenance']['raw_sha256']
 assert hashlib.sha256(o['statement'].encode()).hexdigest()==o['provenance']['statement_utf8_sha256']
print('all 20 raw and statement hashes verified')
# Actual immutable local upstream preprints listing read and bounded terms screen.
p=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/preprints-tree.json');j=json.loads(p.read_text());s=p.read_text();terms=['Kottari','Sahni','Perarnau','Kirgizov','Vlasev','Drinfeld-Yetter','parabolic-non','simplicial-tree','Bressoud','Kanade'];print('upstream hits',{t:t.lower() in s.lower() for t in terms});(D/'outputs/openai-catalogue-read.json').write_text(json.dumps({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'term_hits':{t:t.lower() in s.lower() for t in terms}})+'\n')
manifest={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in D.rglob('*') if p.is_file() and p.name!='artifact-hashes.json'}
(D/'outputs/artifact-hashes.json').write_text(json.dumps(manifest,indent=2)+'\n')
