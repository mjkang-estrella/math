"""Verify bytes independently; write only within the round-6 assignment."""
import hashlib, json, urllib.request
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
ROOT=Path(__file__).resolve().parents[3]
OUT=Path(__file__).resolve().parent
AUTHOR=ROOT/'frontier/sources/i04_operator_asymmetric'
sha=lambda b:hashlib.sha256(b).hexdigest()
blob=lambda b:hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
inputs=['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','frontier/iterations/README.md','frontier/iterations/i04-operator-asymmetric.md','frontier/reviews/i03-operator-halfspace-r4.md','frontier/iterations/i02-operator-r2.md','frontier/reviews/i02-operator-r3.md','frontier/experiments/i04_operator_asymmetric/check.py','frontier/experiments/i04_operator_asymmetric/output.json']
manifest=OUT/'input_manifest.json'
if not manifest.exists():
    manifest.write_text(json.dumps([dict(path=p,sha256=sha((ROOT/p).read_bytes())) for p in inputs],indent=2)+'\n')
tree=json.loads((ROOT/'sources/preprints-tree.json').read_text())
assert not tree['truncated']
entries={r['path']:r.get('sha') for r in tree['tree']}
revision=json.loads((ROOT/'sources/upstream.json').read_text())['commit']
def verify_one(r):
    b=(ROOT/r['file']).read_bytes()
    assert sha(b)==r['sha256'] and blob(b)==r['git_blob_sha1']==entries[r['path']]
    assert '/'+revision+'/' in r['url']
    fresh=urllib.request.urlopen(r['url'],timeout=40).read()
    assert fresh==b
    dest=OUT/Path(r['file']).name;dest.write_bytes(fresh)
    return dict(path=r['path'],url=r['url'],file=str(dest.relative_to(ROOT)),sha256=sha(fresh),git_blob_sha1=blob(fresh),pinned_tree_matches=True,fresh_download_matches=True)
with ThreadPoolExecutor(max_workers=6) as pool:
    upstream=list(pool.map(verify_one,json.loads((AUTHOR/'upstream_manifest.json').read_text())))
literature=[]
for r in json.loads((AUTHOR/'literature_manifest.json').read_text()):
    if r['status']!='downloaded': continue
    b=(ROOT/r['file']).read_bytes()
    assert sha(b)==r['sha256'] and len(b)==r['bytes']
    literature.append(dict(file=r['file'],sha256=sha(b),bytes=len(b),matches=True))
artifacts=[]
for r in json.loads((AUTHOR/'artifact_manifest.json').read_text()):
    actual=sha((ROOT/r['path']).read_bytes())
    assert actual==r['sha256'],r['path']
    artifacts.append(dict(path=r['path'],sha256=actual,matches=True))
old_inputs=[]
for r in json.loads((AUTHOR/'input_manifest.json').read_text()):
    old_inputs.append(dict(path=r['path'],matches=sha((ROOT/r['path']).read_bytes())==r['sha256']))
ours=[]
for r in json.loads(manifest.read_text()):
    ours.append(dict(path=r['path'],matches=sha((ROOT/r['path']).read_bytes())==r['sha256']))
result=dict(revision=revision,upstream=upstream,literature=literature,author_artifacts=artifacts,author_input_versions=old_inputs,reviewer_input_versions=ours,passed=True,scope='Source integrity only, not truth, deduction validity, or priority.')
(OUT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(upstream_files=len(upstream),fresh_downloads=len(upstream),literature_pdfs=len(literature),author_artifacts=len(artifacts),author_input_versions=old_inputs,reviewer_input_versions=ours,passed=True),indent=2))
