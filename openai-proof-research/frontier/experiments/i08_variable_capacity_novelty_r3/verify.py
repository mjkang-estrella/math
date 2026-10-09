"""Verify input identity, pinned Git blobs, and the sealed artifact manifest.

--seal records validation and creates the manifest after report finalization.
Default mode verifies without modifying any file.
"""
import hashlib,json,sys,datetime
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i08_variable_capacity_novelty_r3'
E=ROOT/'frontier/experiments/i08_variable_capacity_novelty_r3'
REPORT=ROOT/'frontier/reviews/i08-variable-capacity-novelty-r3.md'
def sha(b):return hashlib.sha256(b).hexdigest()
m=json.loads((S/'input-manifest.json').read_text())
tree=json.loads((ROOT/'sources/preprints-tree.json').read_text())
assert tree['truncated'] is False
blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
context_changes=[]
for x in m['inputs']:
    current=sha((ROOT/x['path']).read_bytes())
    if current!=x['sha256']:
        # Parent integration may advance the shared index during a delegated audit.
        assert x['path']=='frontier/TEN-FINDINGS.md',x['path']
        context_changes.append(dict(path=x['path'],initial_sha256=x['sha256'],final_sha256=current,explanation='Shared contextual index changed externally during audit; candidate and proof inputs are unchanged.'))
for x in m['sources']:
    b=(ROOT/x['local']).read_bytes()
    assert sha(b)==x['sha256'] and len(b)==x['bytes'],x['local']
    blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    assert blob==x['git_blob']==blobs[x['path']],x['path']
lit=[x for x in json.loads((S/'literature/retrieval-manifest.json').read_text()) if x.get('status')=='ok']
for x in lit:
    b=(S/'literature'/(x['id']+'.pdf')).read_bytes()
    assert sha(b)==x['sha256'] and len(b)==x['bytes'],x['id']
assert json.loads((E/'results.json').read_text())['status']=='PASS'
manifest=S/'artifact-manifest.json'
if '--seal' in sys.argv:
    validation=dict(status='PASS',timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),unchanged_inputs=len(m['inputs'])-len(context_changes),context_changes=context_changes,pinned_sources=len(m['sources']),complete_inventory_entries=len(tree['tree']),primary_pdfs=len(lit),all_source_git_blobs_match=True)
    (S/'verification.json').write_text(json.dumps(validation,indent=2)+'\n')
    paths=sorted(set([REPORT]+[p for d in (S,E) for p in d.rglob('*') if p.is_file() and p!=manifest]))
    records=[dict(path=str(p.relative_to(ROOT)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in paths]
    manifest.write_text(json.dumps(dict(excludes_self=True,artifacts=records),indent=2)+'\n')
records=json.loads(manifest.read_text())['artifacts']
for x in records:
    b=(ROOT/x['path']).read_bytes()
    assert sha(b)==x['sha256'] and len(b)==x['bytes'],x['path']
print(json.dumps(dict(status='PASS',unchanged_inputs=len(m['inputs'])-len(context_changes),context_changes=context_changes,pinned_sources=len(m['sources']),primary_pdfs=len(lit),artifacts=len(records),all_source_git_blobs_match=True)))
