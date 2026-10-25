#!/usr/bin/env python3
"""Read-only exact-selection verifier. Supply detached anchors explicitly."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, stat
OUTSIDE = {
 'MANIFEST.json','REPORT.md','FINAL.sha256','MANIFEST.sha256','REPORT.sha256',
 'private/integrity-controls.json','private/controls/FINAL-copy.md',
 'private/controls/MANIFEST-copy.json'
}
def sha(data): return hashlib.sha256(data).hexdigest()
def file_set(root):
    out=set()
    for p in root.rglob('*'):
        if p.is_symlink(): raise ValueError('symlink forbidden: '+str(p.relative_to(root)))
        if p.is_file(): out.add(p.relative_to(root).as_posix())
    return out

def verify_entries(root, entries, outside=()):
    names=[e['path'] for e in entries]
    if names!=sorted(set(names)): raise ValueError('selection is not sorted and unique')
    if file_set(root)-set(outside)!=set(names): raise ValueError('exact selection mismatch')
    for e in entries:
        rel=PurePosixPath(e['path'])
        if rel.is_absolute() or '..' in rel.parts: raise ValueError('unsafe path')
        p=root/rel
        if p.is_symlink() or not p.is_file(): raise ValueError('not a regular file')
        b=p.read_bytes()
        if len(b)!=e['bytes'] or sha(b)!=e['sha256']: raise ValueError('byte/hash mismatch: '+str(rel))
        if format(stat.S_IMODE(p.stat().st_mode),'04o')!=e['mode']: raise ValueError('mode mismatch: '+str(rel))
    return len(entries)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',required=True)
    ap.add_argument('--manifest-sha256',required=True)
    ap.add_argument('--final-sha256',required=True)
    ap.add_argument('--report-sha256',required=True)
    a=ap.parse_args();root=Path(a.root)
    anchors={'MANIFEST.json':a.manifest_sha256,'FINAL.md':a.final_sha256,'REPORT.md':a.report_sha256}
    for name,digest in anchors.items():
        if len(digest)!=64 or any(c not in '0123456789abcdef' for c in digest): raise ValueError('invalid explicit anchor')
        p=root/name
        if p.is_symlink() or sha(p.read_bytes())!=digest: raise ValueError('detached anchor mismatch: '+name)
        if stat.S_IMODE(p.stat().st_mode)!=0o444: raise ValueError('anchor file mode mismatch: '+name)
    m=json.loads((root/'MANIFEST.json').read_bytes())
    if m['outside_selection']!=sorted(OUTSIDE): raise ValueError('outside selection changed')
    n=verify_entries(root,m['files'],OUTSIDE)
    print(json.dumps({'artifact_verification':'matched supplied anchors, exact selection and file modes','files':n,'mathematical_gate':False}))
if __name__=='__main__': main()
