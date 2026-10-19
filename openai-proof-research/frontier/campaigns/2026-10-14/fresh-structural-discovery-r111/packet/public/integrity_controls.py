#!/usr/bin/env python3
"""Exercise artifact rejections on disposable copies; no mathematical tests."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True


def inventory(root):
    out = []
    for parent, dirs, files in os.walk(root, followlinks=False):
        for name in sorted(dirs + files):
            p = Path(parent) / name
            rel = p.relative_to(root).as_posix()
            if p.is_symlink():
                out.append((rel, 'link', os.readlink(p)))
            elif p.is_dir():
                out.append((rel, 'dir'))
            else:
                out.append((rel, hashlib.sha256(p.read_bytes()).hexdigest()))
    return hashlib.sha256(json.dumps(sorted(out)).encode()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet', required=True, type=Path)
    ap.add_argument('--finalhash', required=True)
    ap.add_argument('--tree', required=True, type=Path)
    ap.add_argument('--workdir', required=True, type=Path)
    a = ap.parse_args()
    packet, work = a.packet.resolve(), a.workdir.resolve()
    if work.parent != packet.parent or work == packet:
        raise ValueError('control workdir must be an outer sibling of packet')
    work.mkdir(exist_ok=True)
    copy = work / 'disposable-copy'
    if copy.exists():
        raise ValueError('refusing to overwrite existing control copy')
    original = inventory(packet)
    results = []
    cases = [
        ('pristine', ''), ('wrong-anchor', 'detached finalhash mismatch'),
        ('missing-anchor', '--finalhash'), ('changed-public', 'payload mismatch'),
        ('missing-file', 'file membership mismatch'),
        ('extra-file', 'file membership mismatch'),
        ('extra-directory', 'directory membership mismatch'),
        ('symlink-file', 'symlink'), ('symlink-directory', 'symlink'),
        ('changed-manifest', 'detached finalhash mismatch'),
        ('changed-verifier', 'payload mismatch'), ('wrong-tree', 'external tree hash'),
    ]
    for case, reason in cases:
        shutil.copytree(packet, copy)
        root = copy / 'public/report.md'
        anchor = a.finalhash
        tree = a.tree
        if case == 'wrong-anchor':
            anchor = ('1' if anchor[0] != '1' else '2') + anchor[1:]
        elif case == 'changed-public':
            root.write_bytes(root.read_bytes() + b'\nchanged\n')
        elif case == 'missing-file':
            root.unlink()
        elif case == 'extra-file':
            (copy / 'extra').write_text('unlisted\n')
        elif case == 'extra-directory':
            (copy / 'empty-extra').mkdir()
        elif case == 'symlink-file':
            root.unlink()
            root.symlink_to('screen-168.md')
        elif case == 'symlink-directory':
            (copy / 'extra-link').symlink_to('public', target_is_directory=True)
        elif case == 'changed-manifest':
            p = copy / 'manifest.json'
            p.write_bytes(p.read_bytes() + b' ')
        elif case == 'changed-verifier':
            p = copy / 'public/verify.py'
            p.write_bytes(p.read_bytes() + b'\n# tampered\n')
        elif case == 'wrong-tree':
            tree = copy / 'private/selected-tree-entries.json'
        before = inventory(copy)
        # Execute the pristine verifier against each changed copy. Its own
        # counterpart inside the copy is also an authenticated payload.
        cmd = [sys.executable, '-B', str(packet / 'public/verify.py'), '--root', str(copy)]
        if case != 'missing-anchor':
            cmd += ['--finalhash', anchor]
        cmd += ['--tree', str(tree)]
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
        after = inventory(copy)
        expected = ((proc.returncode == 0) if case == 'pristine'
                    else proc.returncode != 0 and reason in proc.stderr)
        ok = expected and before == after and inventory(packet) == original
        results.append({'case': case, 'passed': ok, 'returncode': proc.returncode,
                        'expected_reason': reason, 'stdout': proc.stdout.strip(),
                        'stderr': proc.stderr.strip(), 'copy_unchanged_by_verifier': before == after,
                        'copy_before': before, 'copy_after': after})
        shutil.rmtree(copy)
        if not ok:
            break
    receipt = {'controls': results, 'all_passed': len(results) == len(cases)
               and all(r['passed'] for r in results), 'packet_before': original,
               'packet_after': inventory(packet), 'detached_finalhash': a.finalhash,
               'mathematical_gate': False, 'copies_retained': False}
    (work / 'results.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'controls': len(results), 'all_passed': receipt['all_passed'],
                      'packet_unchanged': receipt['packet_before'] == receipt['packet_after'],
                      'mathematical_gate': False}))
    if not receipt['all_passed']:
        sys.exit(1)


if __name__ == '__main__':
    main()
