exec((__import__('pathlib').Path(__file__).parent/'read.py').read_text().split('for name,url in')[0])
get('original-author.pdf','https://personal.strath.ac.uk/sergey.kitaev/Papers/mesh.pdf')
R=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');audit=[];matches=[];terms=re.compile(r'boxed.mesh|2609.13764|Bruhat.*degree|degree.*Bruhat|strict.interleav|Heilbronn|Sudermann|critical.triangles',re.I)
for p in R.rglob('*'):
 if not p.is_file() or L in p.parents:continue
 if not (p.name.lower() in ['summary.md','discovery.md','findings.md','proof.md','ledger.json','next.md'] or 'review' in str(p.relative_to(R)).lower() and p.suffix in ['.md','.json','.txt']):continue
 b=p.read_bytes();audit.append({'path':str(p.relative_to(R)),'sha256':hashlib.sha256(b).hexdigest()});ls=[s for s in b.decode(errors='replace').splitlines() if terms.search(s)]
 if ls:matches.append({'path':str(p.relative_to(R)),'lines':ls[:25]})
(L/'duplicate-expanded.json').write_text(json.dumps({'terms':terms.pattern,'files':audit,'hits':matches},indent=2));print('AUDIT',len(audit),json.dumps(matches)[:13000],flush=True)
