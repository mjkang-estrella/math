"""Verify bytes against recorded source hashes and the accepted pinned tree."""
from pathlib import Path
import hashlib,json

ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).parent
tree={r['path']:r['sha'] for r in json.loads((ROOT/'sources/preprints-tree.json').read_text())['tree']}
rows=[]
for manifest in (ROOT/'frontier/sources/i05_joint_artin/manifest.json',HERE/'new-source-manifest.json',HERE/'literature-manifest.json'):
    for r in json.loads(manifest.read_text()):
        if 'path' not in r or 'sha256' not in r: continue
        p=ROOT/r['path']; b=p.read_bytes(); sha=hashlib.sha256(b).hexdigest()
        assert sha==r['sha256'],str(p)
        row=dict(path=r['path'],sha256=sha)
        if 'upstream_path' in r:
            blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            assert blob==tree[r['upstream_path']]==r['git_blob'],r['upstream_path']
            row.update(upstream_path=r['upstream_path'],git_blob=blob,url=r['url'])
        rows.append(row)
inputs=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','frontier/iterations/README.md','frontier/findings/R006-progression-PD-primitive-root-density.md','frontier/iterations/i03-arithmetic-progressions.md','frontier/reviews/i03-arithmetic-progressions-r4.md','frontier/iterations/i05-joint-artin.md','frontier/experiments/i05_joint_artin/check.py','frontier/experiments/i05_joint_artin/results.json']
snapshot=[dict(path=p,sha256=hashlib.sha256((ROOT/p).read_bytes()).hexdigest()) for p in inputs]
for p in ['frontier/sources/i05_joint_artin/jarviniemi-perucca-web.json','frontier/sources/i05_joint_artin/lenstra-1977.txt','frontier/sources/i05_joint_artin/lenstra-moree-stevenhagen.txt','frontier/sources/i05_joint_artin/moree-ap-v1.txt']:
    snapshot.append(dict(path=p,sha256=hashlib.sha256((ROOT/p).read_bytes()).hexdigest()))
assert (ROOT/'frontier/experiments/i05_joint_artin/results.json').read_bytes()==(ROOT/'frontier/experiments/i06_cubic_reservoir/results.json').read_bytes()
assert (ROOT/'frontier/experiments/i05_joint_artin/check.py').read_bytes()==(ROOT/'frontier/experiments/i06_cubic_reservoir/reproduce_i05.py').read_bytes()
result=dict(pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',verified_sources=rows,input_snapshot=snapshot,i05_reproduction_byte_identical=True,scope='Integrity only; no upstream truth audit.')
(HERE/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(sources=len(rows),pinned=sum('git_blob' in r for r in rows),reproduction=True)))
