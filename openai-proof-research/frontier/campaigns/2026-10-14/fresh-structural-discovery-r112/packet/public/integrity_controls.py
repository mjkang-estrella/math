#!/usr/bin/env python3
"""Run integrity controls on disposable copies only; no mathematical assertions."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

def snapshot(root):
    return {p.relative_to(root).as_posix(): [hashlib.sha256(p.read_bytes()).hexdigest(),
            p.stat().st_mtime_ns, p.stat().st_size] for p in root.rglob('*') if p.is_file()}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--expected-manifest-sha256', required=True)
    parser.add_argument('--tree', type=Path, required=True)
    parser.add_argument('--work-parent', type=Path, required=True)
    args = parser.parse_args()
    before = snapshot(args.packet)
    cases = ['clean-copy', 'missing-detached-argument', 'wrong-detached-anchor',
             'changed-payload', 'missing-payload', 'extra-file', 'extra-directory',
             'symlink', 'changed-manifest', 'self-resealed-payload', 'wrong-tree', 'missing-tree']
    records = []
    for case in cases:
        with tempfile.TemporaryDirectory(prefix='r112-control-', dir=args.work_parent) as temporary:
            temporary = Path(temporary)
            copied = temporary / 'packet'
            shutil.copytree(args.packet, copied)
            expected = args.expected_manifest_sha256
            tree = args.tree.absolute()
            target = copied / 'public/report.md'
            if case == 'wrong-detached-anchor':
                expected = '0' * 64
            elif case in ('changed-payload', 'self-resealed-payload'):
                target.write_bytes(target.read_bytes() + b'\nCONTROL MUTATION\n')
            elif case == 'missing-payload':
                target.unlink()
            elif case == 'extra-file':
                (copied / 'extra.txt').write_text('extra')
            elif case == 'extra-directory':
                (copied / 'extra-empty').mkdir()
            elif case == 'symlink':
                target.unlink()
                target.symlink_to((args.packet / 'public/report.md').absolute())
            elif case == 'changed-manifest':
                manifest = copied / 'manifest.json'
                manifest.write_bytes(manifest.read_bytes() + b' ')
            elif case == 'wrong-tree':
                tree = temporary / 'wrong-tree.json'
                tree.write_text('{}')
            elif case == 'missing-tree':
                tree = temporary / 'absent-tree.json'
            if case == 'self-resealed-payload':
                manifest = copied / 'manifest.json'
                obj = json.loads(manifest.read_text())
                data = target.read_bytes()
                obj['files']['public/report.md'] = {'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}
                manifest.write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n')
            command = [sys.executable, '-B', str(copied / 'public/verify.py'), '--packet', str(copied),
                       '--tree', str(tree)]
            if case != 'missing-detached-argument':
                command += ['--expected-manifest-sha256', expected]
            copied_before = snapshot(copied)
            result = subprocess.run(command, capture_output=True, text=True)
            readonly = snapshot(copied) == copied_before
            passed = readonly and ((result.returncode == 0) == (case == 'clean-copy'))
            records.append({'case': case, 'passed': passed, 'returncode': result.returncode,
                            'read_only_content_size_mtime': readonly,
                            'stdout': result.stdout.strip(), 'stderr': result.stderr.strip()})
    unchanged = before == snapshot(args.packet)
    print(json.dumps({'integrity_only': True, 'original_unchanged': unchanged, 'controls': records,
                      'detached_manifest_sha256': args.expected_manifest_sha256}, indent=2))
    return 0 if unchanged and all(x['passed'] for x in records) else 1

if __name__ == '__main__':
    sys.exit(main())
