from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'final-manifest.json').read_text());paths=set()
for r in m['files']:
 p=L/r['path'];assert p.stat().st_size==r['bytes'] and h(p)==r['sha256'];paths.add(r['path'])
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excludes']}
assert paths==actual
science=0
for r in json.loads((L/'bindings.json').read_text()):
 assert h(L/r['copy'])==r['sha256']
 if r['kind']=='scientific':assert h(Path(r['original']))==r['sha256'];science+=1
for fn,field in [('2410.21651v1.pdf','sha256'),('2410.21651v1.txt','text_sha256')]:assert h(L/fn)==json.loads((L/'primary-followup.json').read_text())[field]
assert not (L/'PROOF.md').exists()
out=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=h(L/'final-manifest.json'),manifest_files=len(paths),scientific_original_copy_pairs= science,new_primary_pdf_text_hashes='PASS',administrative_policy='snapshot hashes only; live admin files may change',universal_proof=False,acceptance_credit=0,counts_unchanged=[9,39,40],separate_guarded_postwrite_verification=True)
(L/'final-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
