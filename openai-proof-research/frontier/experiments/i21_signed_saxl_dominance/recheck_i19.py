"""Read-only independent recheck of retained I19 evidence; writes only I21."""
from pathlib import Path
import sys,json,hashlib,importlib.util
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[3];S=ROOT/'frontier/sources/i21_signed_saxl_dominance';P=ROOT/'frontier/sources/i19_fresh_structural_discovery';E=Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
a=json.loads((S/'inputs/frontier/sources/i19_fresh_structural_discovery/artifact-seal.json').read_text())
for p,z in a['files'].items():assert h((ROOT/p).read_bytes())==z,p
pin=json.loads((S/'inputs/frontier/sources/i19_fresh_structural_discovery/pinned-manifest.json').read_text())
tree=json.loads((S/'inputs/sources/preprints-tree.json').read_text());blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
for x in pin:
 b=(P/'pinned'/x['path']).read_bytes();assert h(b)==x['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==blobs[x['path']]
ct=json.loads((S/'inputs/frontier/sources/i19_fresh_structural_discovery/theorem-contracts.json').read_text())
for x in ct:
 t='\n'.join((P/'pinned'/x['path']).read_text().splitlines()[x['start_line']-1:x['end_line']]);assert t==x['text'] and h(t.encode())==x['sha256']
spec=importlib.util.spec_from_file_location('prior',S/'inputs/frontier/experiments/i19_fresh_structural_discovery/check.py');prior=importlib.util.module_from_spec(spec);spec.loader.exec_module(prior)
r=prior.main();expected=json.loads((S/'inputs/frontier/experiments/i19_fresh_structural_discovery/results.json').read_text());assert json.loads(json.dumps(r))==expected
out=dict(sealed_artifacts=len(a['files']),pinned_files=len(pin),source_contracts=len(ct),two_row_character_checks=r['band_character_checks'],signed_bounds=r['signed_lower_bound_checks'],orthogonality_checks=r['character_orthogonality_checks'],literal_projection_cases=len(r['tensor_projection_cases']),diagnostics_reproduced=True,disposition='technical validation only; no independent proof/significance acceptance')
(E/'i19-recheck.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
