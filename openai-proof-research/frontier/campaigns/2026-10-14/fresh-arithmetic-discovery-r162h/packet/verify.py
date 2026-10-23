"""Read-only verification of an exact packet against three explicit detached anchors."""
import argparse,hashlib,json
from pathlib import Path
ap=argparse.ArgumentParser()
ap.add_argument('--root',required=True)
for k in ['final','manifest','report']:ap.add_argument('--'+k+'-sha256',required=True)
a=ap.parse_args();r=Path(a.root).resolve()
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for key,p in [('final',r/'packet/FINAL.md'),('manifest',r/'MANIFEST.json'),('report',r/'REPORT.md')]:
    assert p.is_file() and not p.is_symlink(), 'missing or symlink anchor '+key
    assert digest(p)==getattr(a,key+'_sha256'), 'detached anchor mismatch '+key
m=json.loads((r/'MANIFEST.json').read_text())
assert m['schema']=='exact-packet-v1'
seen=set()
for row in m['files']:
    rel=Path(row['path'])
    assert not rel.is_absolute() and '..' not in rel.parts and rel.as_posix() not in seen
    seen.add(rel.as_posix())
    p=r/'packet'/rel
    assert not any(q.is_symlink() for q in [p,*p.parents] if q!=r.parent)
    assert p.is_file(), 'missing '+str(rel)
    assert p.stat().st_size==row['bytes'] and digest(p)==row['sha256'], 'changed '+str(rel)
nodes=list((r/'packet').rglob('*'))
assert all(not p.is_symlink() for p in nodes), 'symlink in packet'
actual={p.relative_to(r/'packet').as_posix() for p in nodes if p.is_file()}
assert seen==actual, 'packet membership mismatch'
print(json.dumps({'artifact_only':True,'files':len(seen),'bytes':sum(x['bytes'] for x in m['files']),'anchors':'matched','membership':'exact'}))
