#!/usr/bin/env python3
"""Read-only artifact verifier. Supply all three detached anchors explicitly.

Does not execute research/acquisition code, write receipts, or judge mathematics.
Only scratch/copied-controls is outside the artifact's exact file inventory.
"""
import argparse
import fnmatch
import hashlib
import json
import os
from pathlib import Path, PurePosixPath

ENVELOPES = {'FINAL.md', 'REPORT.md', 'MANIFEST.json', 'ANCHORS.sha256'}
OUTSIDE = 'scratch/copied-controls'
ACTIVE = ['*structural*r144*', '*analytic*r138*', '*t185r144-*', '*h138-*']
TREE_SHA = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'


def digest(b):
    return hashlib.sha256(b).hexdigest()


def inventory(root):
    found = set()
    for directory, dirs, files in os.walk(root, followlinks=False):
        kept = []
        for name in sorted(dirs):
            p = Path(directory) / name
            rel = p.relative_to(root).as_posix()
            assert not any(fnmatch.fnmatch(name.lower(), pat) for pat in ACTIVE), 'excluded active component'
            assert not p.is_symlink(), 'symlink directory'
            if rel != OUTSIDE:
                kept.append(name)
        dirs[:] = kept
        for name in sorted(files):
            assert not any(fnmatch.fnmatch(name.lower(), pat) for pat in ACTIVE), 'excluded active filename'
            p = Path(directory) / name
            assert p.is_file() and not p.is_symlink(), 'nonregular or symlink file'
            found.add(p.relative_to(root).as_posix())
    return found


def verify(root, anchors):
    assert root.is_dir() and not root.is_symlink(), 'root must be a real directory'
    for name, expected in anchors.items():
        assert len(expected) == 64 and all(c in '0123456789abcdef' for c in expected), 'invalid anchor'
        p = root / name
        assert not p.is_symlink(), 'symlink envelope'
        assert digest(p.read_bytes()) == expected, 'detached anchor mismatch: ' + name
    text = ''.join(anchors[n] + '  ' + n + '\n' for n in ['FINAL.md', 'MANIFEST.json', 'REPORT.md'])
    assert (root / 'ANCHORS.sha256').read_text() == text, 'anchor receipt mismatch'
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    assert manifest['format'] == 'r109-exact-payload-v1'
    assert manifest['outside_control_subtree'] == OUTSIDE
    seen = set()
    for row in manifest['files']:
        s = row['path']
        p = PurePosixPath(s)
        assert s == p.as_posix() and not p.is_absolute() and '..' not in p.parts and '.' not in p.parts, 'unsafe path'
        assert s not in seen and s not in ENVELOPES and not s.startswith(OUTSIDE + '/'), 'duplicate/envelope/control path'
        seen.add(s)
    assert inventory(root) == seen | ENVELOPES, 'exact membership mismatch'
    for row in manifest['files']:
        b = (root / row['path']).read_bytes()
        assert len(b) == row['bytes'] and digest(b) == row['sha256'], 'payload mismatch: ' + row['path']
    tree_bytes = (root / 'private/history/initial-02-preprints-tree.json').read_bytes()
    assert digest(tree_bytes) == TREE_SHA, 'complete tree digest'
    tree = json.loads(tree_bytes)
    assert len(tree['tree']) == 13223 and not tree.get('truncated', False), 'complete tree extent'
    entries = {e['path']: e for e in tree['tree']}
    metadata = json.loads((root / 'private/source/metadata.json').read_text())
    assert len(metadata) == 25, 'source acquisition count'
    for row in metadata:
        b = (root / row['local']).read_bytes()
        # The complete preprints tree may use paths relative to preprints/.
        e = entries.get(row['path'], entries.get(row['path'].removeprefix('preprints/')))
        assert e is not None, 'canonical source path absent'
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        assert len(b) == row['bytes'] == e['size'], 'source size'
        assert blob == row['git_blob'] == e['sha'], 'source blob'
        assert digest(b) == row['sha256'], 'source sha256'
    return {'artifact_integrity': 'verified', 'payload_files': len(seen), 'authenticated_pinned_blobs': len(metadata), 'mathematical_gate': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    try:
        result = verify(args.root.absolute(), {'FINAL.md': args.final_sha256, 'MANIFEST.json': args.manifest_sha256, 'REPORT.md': args.report_sha256})
    except (AssertionError, KeyError, ValueError, OSError) as exc:
        print(json.dumps({'artifact_integrity': 'rejected', 'reason': str(exc)}))
        raise SystemExit(1)
    print(json.dumps(result, sort_keys=True))
