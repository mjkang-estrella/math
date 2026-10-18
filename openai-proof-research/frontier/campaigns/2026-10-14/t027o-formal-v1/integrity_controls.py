#!/usr/bin/env python3
"""MIT, Myeongjin Kang. Identity controls on disposable copies only."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).absolute().parent

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--anchor', required=True)
    args = parser.parse_args()
    def run(root, anchor):
        return subprocess.run(['python3', '-B', str(root / 'verify.py'), '--anchor', anchor],
                              text=True, capture_output=True)
    original = run(ROOT, args.anchor)
    if original.returncode:
        raise ValueError(original.stderr)
    cases = ['positive', 'wrong-anchor', 'changed-source', 'missing-source', 'extra-file',
             'extra-directory', 'root-link', 'ancestor-link', 'payload-link',
             'payload-hardlink', 'fifo', 'manifest-hardlink', 'nested-manifest', 'self-reseal']
    results = []
    with tempfile.TemporaryDirectory(prefix='t027o-formal-controls-', dir='/var/tmp') as tmp:
        base = Path(tmp)
        for case in cases:
            dest = base / case
            shutil.copytree(ROOT, dest)
            source = dest / 'T027O.lean'
            anchor = args.anchor
            if case == 'wrong-anchor': anchor = '0' * 64
            elif case == 'changed-source': source.write_bytes(source.read_bytes() + b'\n-- changed\n')
            elif case == 'missing-source': source.unlink()
            elif case == 'extra-file': (dest / 'extra').write_text('extra')
            elif case == 'extra-directory': (dest / 'extra').mkdir()
            elif case == 'root-link':
                link = base / 'root-alias'; link.symlink_to(dest, target_is_directory=True); dest = link
            elif case == 'ancestor-link':
                link = base / 'ancestor-alias'; link.symlink_to(base, target_is_directory=True); dest = link / case
            elif case == 'payload-link': source.unlink(); source.symlink_to('Controls.lean')
            elif case == 'payload-hardlink': os.link(source, base / 'linked-source')
            elif case == 'fifo': source.unlink(); os.mkfifo(source)
            elif case == 'manifest-hardlink': os.link(dest / 'manifest.json', base / 'linked-manifest')
            elif case == 'nested-manifest': (dest / 'checks/manifest.json').write_text('{}')
            elif case == 'self-reseal':
                source.write_bytes(source.read_bytes() + b'\n-- changed\n')
                manifest = json.loads((dest / 'manifest.json').read_text())
                data = source.read_bytes()
                manifest['files']['T027O.lean'] = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
                (dest / 'manifest.json').write_text(json.dumps(manifest))
            result = run(dest, anchor)
            accepted = result.returncode == 0
            if accepted != (case == 'positive'):
                raise AssertionError((case, result.returncode, result.stdout, result.stderr))
            results.append({'case': case, 'accepted': accepted})
    print(json.dumps({'identity_only': True, 'results': results}, indent=2))

if __name__ == '__main__':
    main()
