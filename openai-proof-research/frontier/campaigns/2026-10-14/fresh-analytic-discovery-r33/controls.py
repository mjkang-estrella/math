#!/usr/bin/env python3
"""MIT; actual copied-file integrity controls. Writes temporary copies only."""
import argparse, hashlib, json, shutil, subprocess, sys, tempfile
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--anchor', required=True)
    a = ap.parse_args()
    root = Path(__file__).absolute().parent
    def run(p, anchor):
        return subprocess.run([sys.executable, str(p/'verify.py'), '--root', str(p), '--anchor', anchor], capture_output=True, text=True)
    first = run(root, a.anchor)
    if first.returncode:
        raise SystemExit(first.stdout + first.stderr)
    checks = {'positive': True, 'wrong_anchor': run(root, '0'*64).returncode != 0}
    manifest = json.loads((root/'manifest.json').read_text())
    with tempfile.TemporaryDirectory(prefix='.controls-', dir=root) as td:
        work = Path(td)
        def copy_packet(name):
            p = work/name
            p.mkdir()
            for d in manifest['directories']:
                (p/d).mkdir(parents=True, exist_ok=True)
            for f in list(manifest['files']) + ['manifest.json']:
                shutil.copyfile(root/f, p/f)
            return p
        p = copy_packet('unchanged')
        checks['copied_positive'] = run(p, a.anchor).returncode == 0
        tests = {
            'changed_payload': lambda p: (p/'report.md').write_text((p/'report.md').read_text()+'CORRUPTED\n'),
            'missing_payload': lambda p: (p/'report.md').unlink(),
            'extra_payload': lambda p: (p/'extra.txt').write_text('extra'),
            'extra_directory': lambda p: (p/'empty-extra').mkdir(),
            'nested_manifest_name': lambda p: (p/'private/manifest.json').write_text('{}'),
            'symlink': lambda p: (p/'unexpected-link').symlink_to('report.md'),
            'hardlink': lambda p: (p/'unexpected-hardlink').hardlink_to(p/'report.md'),
        }
        for name, mutation in tests.items():
            p = copy_packet(name)
            mutation(p)
            checks[name+'_rejected'] = run(p, a.anchor).returncode != 0
    last = run(root, a.anchor)
    checks['original_after_cleanup'] = last.returncode == 0
    if not all(checks.values()):
        print(json.dumps(checks, sort_keys=True)); raise SystemExit(1)
    print(json.dumps({'status': 'PASS_CONTROLS_INTEGRITY_ONLY', 'manifest_sha256': a.anchor, 'checks': checks}, sort_keys=True))

if __name__ == '__main__':
    main()
