#!/usr/bin/env python3
"""Read-only exact selected-packet verifier; no mathematical verdict."""
import argparse, hashlib, json, stat
from pathlib import Path

ENVELOPES = {'FINAL.md', 'MANIFEST.json', 'REPORT.md'}
def sha(b):
    return hashlib.sha256(b).hexdigest()
def inventory(root):
    files, dirs = {}, []
    def visit(base):
        for p in sorted(base.iterdir()):
            rel = p.relative_to(root).as_posix()
            s = p.lstat()
            if stat.S_ISLNK(s.st_mode):
                raise ValueError('symlink forbidden: '+rel)
            if stat.S_ISDIR(s.st_mode):
                dirs.append(rel)
                visit(p)
            elif stat.S_ISREG(s.st_mode):
                if rel not in ENVELOPES:
                    b = p.read_bytes()
                    files[rel] = {'path': rel, 'bytes': len(b), 'sha256': sha(b), 'mode': stat.S_IMODE(s.st_mode)}
            else:
                raise ValueError('nonregular object: '+rel)
    visit(root)
    return files, sorted(dirs)
def verify(root, anchors):
    for name, digest in anchors.items():
        p = root/name
        if p.is_symlink() or not p.is_file() or sha(p.read_bytes()) != digest:
            raise ValueError('envelope anchor mismatch: '+name)
    m = json.loads((root/'MANIFEST.json').read_text())
    if m['format'] != 'analytic161-independent-selected-packet-v1' or set(m['outside_envelopes']) != ENVELOPES:
        raise ValueError('wrong schema/envelopes')
    expected = {x['path']: x for x in m['files']}
    if len(expected) != len(m['files']):
        raise ValueError('duplicate manifest member')
    actual, dirs = inventory(root)
    if set(expected) != set(actual):
        raise ValueError('file membership mismatch: '+str({'missing': sorted(set(expected)-set(actual)), 'extra': sorted(set(actual)-set(expected))}))
    if dirs != m['directories']:
        raise ValueError('directory membership mismatch')
    for name, entry in actual.items():
        if entry != expected[name]:
            raise ValueError('payload identity/mode mismatch: '+name)
    return {'verified': True, 'payload_files': len(actual), 'directories': len(dirs), 'envelopes': 3, 'meaning': 'bytes and membership only; no mathematical judgment'}
if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    for name in ['final', 'manifest', 'report']:
        p.add_argument('--'+name+'-sha256', required=True)
    a = p.parse_args()
    try:
        result = verify(a.root.resolve(), {'FINAL.md': a.final_sha256, 'MANIFEST.json': a.manifest_sha256, 'REPORT.md': a.report_sha256})
        print(json.dumps(result, sort_keys=True))
    except Exception as e:
        print(json.dumps({'verified': False, 'reason': str(e)}, sort_keys=True))
        raise SystemExit(1)
