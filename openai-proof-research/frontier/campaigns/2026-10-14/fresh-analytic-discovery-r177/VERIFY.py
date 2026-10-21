"""Read-only selected-packet integrity check. No mathematical assertions."""
import argparse, hashlib, json
from pathlib import Path, PurePosixPath

def sha(b):
    return hashlib.sha256(b).hexdigest()

def verify(root, final_sha, manifest_sha, report_sha):
    root=Path(root).resolve()
    for name,expected in [('FINAL.md',final_sha),('MANIFEST.json',manifest_sha),('REPORT.md',report_sha)]:
        p=root/name
        if p.is_symlink() or not p.is_file():
            raise ValueError('missing or linked detached object: '+name)
        if sha(p.read_bytes())!=expected:
            raise ValueError('detached anchor mismatch: '+name)
    manifest=json.loads((root/'MANIFEST.json').read_bytes())
    if manifest['algorithm']!='sha256':raise ValueError('algorithm')
    seen=set()
    for item in manifest['files']:
        rel=item['path'];parts=PurePosixPath(rel)
        if parts.is_absolute() or '..' in parts.parts or str(parts)!=rel or rel in seen:
            raise ValueError('unsafe or repeated selected path')
        seen.add(rel);p=root.joinpath(*parts.parts)
        if any(root.joinpath(*parts.parts[:i]).is_symlink() for i in range(1,len(parts.parts)+1)):
            raise ValueError('linked selected path: '+rel)
        b=p.read_bytes()
        if len(b)!=item['bytes'] or sha(b)!=item['sha256']:
            raise ValueError('selected entry mismatch: '+rel)
    if 'FINAL.md' not in seen:raise ValueError('FINAL not selected')
    return len(seen)

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',required=True)
    ap.add_argument('--final-sha256',required=True)
    ap.add_argument('--manifest-sha256',required=True)
    ap.add_argument('--report-sha256',required=True)
    a=ap.parse_args()
    n=verify(a.root,a.final_sha256,a.manifest_sha256,a.report_sha256)
    print('Artifact digests match:',n,'selected files; no mathematical gate.')
