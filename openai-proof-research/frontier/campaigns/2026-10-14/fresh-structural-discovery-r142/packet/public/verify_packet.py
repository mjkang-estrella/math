"""Read-only artifact verifier. Requires three externally supplied SHA256 anchors.
Not a mathematical verifier, independent review, formal gate, or acceptance.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath

ENVELOPES = {'MANIFEST.json', 'FINAL.json', 'outsideREPORT.md', 'ANCHORS.json'}

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def verify(root, manifest_sha, final_sha, report_sha):
    if root.is_symlink():
        raise ValueError('Root symlink not allowed')
    actual = set()
    for p in root.rglob('*'):
        if p.is_symlink():
            raise ValueError('Symlink not allowed: '+str(p))
        if p.is_file():
            actual.add(p.relative_to(root).as_posix())
    expected = {'MANIFEST.json': manifest_sha, 'FINAL.json': final_sha,
                'outsideREPORT.md': report_sha}
    for name, sha in expected.items():
        if len(sha) != 64 or digest(root/name) != sha:
            raise ValueError('Detached anchor mismatch: '+name)
    records = json.loads((root/'MANIFEST.json').read_text())['files']
    names = set()
    for row in records:
        name = row['path']
        q = PurePosixPath(name)
        if q.is_absolute() or '..' in q.parts or str(q) != name or name in ENVELOPES or name in names:
            raise ValueError('Invalid inventory path: '+name)
        names.add(name)
        p = root/name
        if p.stat().st_size != row['bytes'] or digest(p) != row['sha256']:
            raise ValueError('Payload mismatch: '+name)
    if actual != names | ENVELOPES:
        raise ValueError('Exact membership mismatch')
    final = json.loads((root/'FINAL.json').read_text())
    if final['manifest_sha256'] != manifest_sha or final['outside_report_sha256'] != report_sha:
        raise ValueError('FINAL linkage mismatch')
    anchors = json.loads((root/'ANCHORS.json').read_text())
    if anchors != expected:
        raise ValueError('Stored anchors disagree with explicit detached anchors')
    return len(records)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', type=Path)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    count = verify(args.root, args.manifest_sha256, args.final_sha256, args.report_sha256)
    print(json.dumps({'artifact_integrity': 'matched', 'payload_files': count,
                      'mathematical_gate': False}))
