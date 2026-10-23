#!/usr/bin/env python3
"""Read-only verification of one exact packet and three mandatory detached anchors.
No writes, repair, chmod, manifest generation, network, or inferred anchors.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys
sys.dont_write_bytecode = True


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def snapshot(root):
    entries = []
    def visit(path, rel):
        st = path.lstat()
        mode = format(stat.S_IMODE(st.st_mode), '04o')
        if stat.S_ISDIR(st.st_mode):
            entries.append({'path': rel, 'type': 'directory', 'mode': mode})
            with os.scandir(path) as scan:
                children = sorted(scan, key=lambda e: e.name)
            for child in children:
                visit(Path(child.path), rel + '/' + child.name if rel else child.name)
        elif stat.S_ISREG(st.st_mode):
            entries.append({'path': rel, 'type': 'file', 'mode': mode,
                            'size': st.st_size, 'sha256': sha(path)})
        else:
            raise ValueError('nonregular file or symlink: ' + rel)
    visit(root, '')
    return sorted(entries, key=lambda e: e['path'])


def verify(args):
    for value in [args.final_sha256, args.manifest_sha256, args.report_sha256]:
        if len(value) != 64 or any(ch not in '0123456789abcdef' for ch in value):
            raise ValueError('three explicit lowercase literal SHA256 anchors required')
    for path in [args.manifest, args.report, args.packet / 'FINAL.md']:
        if not stat.S_ISREG(path.lstat().st_mode):
            raise ValueError('nonregular anchor path')
    for name, path, value in [('FINAL', args.packet / 'FINAL.md', args.final_sha256),
                              ('MANIFEST', args.manifest, args.manifest_sha256),
                              ('REPORT', args.report, args.report_sha256)]:
        if sha(path) != value:
            raise ValueError(name + ' detached anchor mismatch')
    manifest = json.loads(args.manifest.read_text())
    if manifest.get('format') != 'structural-r203-proof-r1-exact-v1':
        raise ValueError('unsupported manifest format')
    if manifest.get('packet_root') != args.packet.name:
        raise ValueError('packet root identity mismatch')
    entries = manifest.get('entries')
    if not isinstance(entries, list):
        raise ValueError('missing entry list')
    seen = set()
    for e in entries:
        rel = e['path']
        pp = PurePosixPath(rel)
        if rel in seen or (rel and (pp.is_absolute() or '..' in pp.parts or pp.as_posix() != rel)):
            raise ValueError('unsafe or duplicate selected path')
        seen.add(rel)
    actual = snapshot(args.packet)
    if actual != sorted(entries, key=lambda e: e['path']):
        exp = {e['path']: e for e in entries}
        act = {e['path']: e for e in actual}
        raise ValueError('exact selection/type/mode/byte mismatch: ' + json.dumps({
            'missing': sorted(set(exp) - set(act)), 'extra': sorted(set(act) - set(exp)),
            'changed': [p for p in sorted(set(exp) & set(act)) if exp[p] != act[p]]}))
    return {'verified': True, 'files': sum(e['type'] == 'file' for e in actual),
            'directories': sum(e['type'] == 'directory' for e in actual),
            'content_bytes': sum(e.get('size', 0) for e in actual),
            'meaning': 'Exact artifact identity only, not a mathematical grade.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['packet', 'manifest', 'report']:
        parser.add_argument('--' + name, type=Path, required=True)
    for name in ['final', 'manifest', 'report']:
        parser.add_argument('--' + name + '-sha256', required=True)
    args = parser.parse_args()
    try:
        print(json.dumps(verify(args), sort_keys=True))
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
