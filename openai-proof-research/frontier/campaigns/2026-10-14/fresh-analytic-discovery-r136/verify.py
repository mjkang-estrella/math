"""Read-only artifact verifier. Requires three independently provided SHA256 anchors."""
import argparse,hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parent
P=R.parents[3]
OUT={'MANIFEST.json','FINAL.md','REPORT.md','DETACHED.json'}
def sha(b):return hashlib.sha256(b).hexdigest()
def data(p):return json.loads(p.read_text())
def check(ok,msg):
 if not ok:raise SystemExit('ARTIFACT MISMATCH: '+msg)
p=argparse.ArgumentParser();p.add_argument('--manifest-sha',required=True);p.add_argument('--final-sha',required=True);p.add_argument('--report-sha',required=True);a=p.parse_args()
anchors={'MANIFEST.json':a.manifest_sha,'FINAL.md':a.final_sha,'REPORT.md':a.report_sha}
for name,anchor in anchors.items():
 check(len(anchor)==64 and all(c in '0123456789abcdef' for c in anchor),'invalid anchor '+name)
 check(sha((R/name).read_bytes())==anchor,'detached '+name)
check(data(R/'DETACHED.json')==anchors,'DETACHED.json disagreement')
m=data(R/'MANIFEST.json');rows=m['files'];names=[x['path'] for x in rows]
check(names==sorted(set(names)),'manifest ordering/duplicates')
actual=set()
for f in R.rglob('*'):
 check(not f.is_symlink(),'symlink '+str(f))
 if f.is_file():actual.add(str(f.relative_to(R)))
check(actual==set(names)|OUT,'exact membership')
for row in rows:
 rel=Path(row['path']);check(not rel.is_absolute() and '..' not in rel.parts,'unsafe path')
 b=(R/rel).read_bytes();check(len(b)==row['size'] and sha(b)==row['sha256'],'payload '+str(rel))
tree_path=R/'private/controls/preprints-tree.json'
check(sha(tree_path.read_bytes())=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','complete tree')
t=data(tree_path);check(not t['truncated'] and len(t['tree'])==13223,'tree extent');tree={x['path']:x for x in t['tree']}
for row in data(R/'source-ledger.json'):
 b=(R/row['local_path']).read_bytes();entry=tree[row['canonical_path']]
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 check(blob==row['git_blob']==entry['sha'] and len(b)==row['size']==entry['size'] and sha(b)==row['sha256'],'source binding '+row['canonical_path'])
 check('/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in row['url'],'source pin URL')
current=[]
for row in data(R/'current-original-checks.json'):
 f=P/row['original_path'];b=f.read_bytes() if f.exists() else None
 h=sha(b) if b is not None else None
 current.append(dict(path=row['original_path'],matches_copy=h==row['copy_sha256'],matches_recorded_current=h==row['current_sha256'],current_sha256=h,mutable_campaign_ledger=row['mutable_campaign_ledger']))
print(json.dumps(dict(artifact_integrity='verified; not a mathematical gate',payload_files=len(rows),source_bindings=len(data(R/'source-ledger.json')),current_originals=current),indent=2))
