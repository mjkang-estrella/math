"""Read-only integrity checks plus an assigned-directory verification record."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];OUT=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
tree=json.loads((ROOT/'sources/preprints-tree.json').read_text())
assert not tree['truncated']
entries={r['path']:r.get('sha') for r in tree['tree']}
upstream=[]
for r in json.loads((OUT/'upstream_manifest.json').read_text()):
    b=(ROOT/r['file']).read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    result=dict(path=r['path'],sha256_matches=sha(b)==r['sha256'],blob_matches=blob==r['git_blob_sha1'],pinned_tree_matches=blob==entries[r['path']])
    assert all(result[k] for k in ['sha256_matches','blob_matches','pinned_tree_matches']);upstream.append(result)
lit=[]
for r in json.loads((OUT/'literature_manifest.json').read_text()):
    if r['status']!='downloaded':continue
    b=(ROOT/r['file']).read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes']
    lit.append(dict(file=r['file'],sha256_matches=True))
inputs=[]
for r in json.loads((OUT/'input_manifest.json').read_text()):
    inputs.append(dict(path=r['path'],current_matches_read_version=sha((ROOT/r['path']).read_bytes())==r['sha256']))
report=ROOT/'frontier/iterations/i04-operator-asymmetric.md'
local_links=[]
for target in re.findall(r'\]\(([^)]+)\)',report.read_text()):
    if '://' in target:continue
    f=(report.parent/target).resolve();assert f.is_file(),target
    local_links.append(target)
artifact_count=0
p=OUT/'artifact_manifest.json'
if p.exists():
    for r in json.loads(p.read_text()):
        assert sha((ROOT/r['path']).read_bytes())==r['sha256'],r['path'];artifact_count+=1
result=dict(upstream=upstream,literature=lit,input_versions=inputs,valid_local_links=len(local_links),artifact_hashes_verified=artifact_count,all_required_integrity_checks_passed=True)
(OUT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(upstream_files=len(upstream),literature_pdfs=len(lit),local_links=len(local_links),artifact_hashes_verified=artifact_count,input_versions=inputs,passed=True),indent=2))
