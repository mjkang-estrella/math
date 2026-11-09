#!/usr/bin/env python3
"""Read-only exact-packet verifier; no writes, implicit anchors, or math gates."""
import argparse
import hashlib
import json
from pathlib import Path

def sha(b):
    return hashlib.sha256(b).hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',required=True)
    ap.add_argument('--manifest-sha',required=True)
    ap.add_argument('--final-sha',required=True)
    ap.add_argument('--report-sha',required=True)
    a=ap.parse_args()
    root=Path(a.root).resolve()
    for rel,want in [('MANIFEST.json',a.manifest_sha),('private/FINAL.md',a.final_sha),('REPORT.md',a.report_sha)]:
        assert len(want)==64 and sha((root/rel).read_bytes())==want, 'detached anchor mismatch: '+rel
    m=json.loads((root/'MANIFEST.json').read_text())
    entries=m['files']
    names={x['path'] for x in entries}
    assert len(names)==len(entries), 'duplicate paths'
    actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
    assert actual==names|{'MANIFEST.json','REPORT.md'}, 'root membership mismatch'
    for row in entries:
        rel=Path(row['path'])
        assert not rel.is_absolute() and '..' not in rel.parts
        p=root/rel
        assert not p.is_symlink() and p.is_file()
        b=p.read_bytes()
        assert len(b)==row['bytes'] and sha(b)==row['sha256'], 'payload mismatch: '+str(rel)
        assert p.stat().st_mode & 0o7777 == row['mode'], 'mode mismatch: '+str(rel)
    tree={e['path']:e for e in json.loads((root/'private/source-tree.json').read_text())}
    auth=json.loads((root/'private/authentication.json').read_text())
    assert len(auth)==27
    for row in auth:
        b=(root/'private/canonical'/row['path']).read_bytes()
        e=tree[row['path']]
        assert len(b)==row['bytes']==e['size']
        assert sha(b)==row['sha256']
        assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']==row['git_blob']
    c=root/'private/controls'
    spec=json.loads((c/'expected.json').read_text())
    assert sha((c/'good.bin').read_bytes())==spec['expected_sha256']
    assert sha((c/'corrupt-copy.bin').read_bytes())!=spec['expected_sha256']
    print(json.dumps({'artifact_check':'PASS','payload_files':len(entries),'payload_bytes':sum(x['bytes'] for x in entries),'canonical_texts':len(auth),'tiny_copy_controls':'expected accept/reject','mathematical_gate':False}))

if __name__=='__main__':
    main()
