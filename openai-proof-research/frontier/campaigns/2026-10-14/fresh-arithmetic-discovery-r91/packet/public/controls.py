#!/usr/bin/env python3
"""Disposable-copy controls; writes only beneath the supplied r91 root. MIT."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys

sys.dont_write_bytecode = True


def snapshot(root):
    rows = []
    for dp, dns, fns in os.walk(root, followlinks=False):
        dns[:] = [n for n in dns if not (Path(dp) == root and n == 'control-work')]
        p = Path(dp)
        s = p.lstat()
        rows.append((str(p.relative_to(root)), 'dir', stat.S_IMODE(s.st_mode)))
        for n in sorted(dns + fns):
            f = p / n
            if p == root and n in ('control-work', 'integrity-results.json'):
                continue
            s = f.lstat()
            if stat.S_ISDIR(s.st_mode):
                continue
            content = os.readlink(f) if stat.S_ISLNK(s.st_mode) else hashlib.sha256(f.read_bytes()).hexdigest()
            rows.append((str(f.relative_to(root)), s.st_mode, s.st_nlink, s.st_size, content))
    return hashlib.sha256(json.dumps(sorted(rows), sort_keys=True).encode()).hexdigest()


def append(f):
    with f.open('ab') as stream:
        stream.write(b'\n# control mutation\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--tree', type=Path, required=True)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    a = ap.parse_args()
    root = a.root.absolute()
    scratch = root / 'control-work'
    if scratch.exists():
        raise RuntimeError('refusing existing control-work')
    before = snapshot(root)
    scratch.mkdir()
    cases = ['baseline', 'payload_change', 'payload_delete', 'extra_file', 'extra_directory',
             'manifest_change', 'final_change', 'report_change', 'wrong_final_anchor',
             'wrong_report_anchor', 'verifier_change', 'canonical_metadata', 'primary_pdf',
             'copied_tree', 'history_body', 'payload_symlink', 'payload_hardlink', 'payload_mode']
    results = []
    try:
        for case in cases:
            dest = scratch / case
            shutil.copytree(root, dest, ignore=shutil.ignore_patterns('control-work', 'integrity-results.json'))
            packet = dest / 'packet'
            target = packet / 'public/tensor-feasibility.md'
            fh, rh = a.final_sha256, a.report_sha256
            if case == 'payload_change': append(target)
            elif case == 'payload_delete': target.unlink()
            elif case == 'extra_file': (packet / 'extra').write_text('control')
            elif case == 'extra_directory': (packet / 'extra-empty').mkdir()
            elif case == 'manifest_change': append(packet / 'MANIFEST.json')
            elif case == 'final_change': append(dest / 'FINAL.json')
            elif case == 'report_change': append(dest / 'REPORT.md')
            elif case == 'wrong_final_anchor': fh = '0' * 64
            elif case == 'wrong_report_anchor': rh = '0' * 64
            elif case == 'verifier_change': append(packet / 'public/verify.py')
            elif case == 'canonical_metadata': append(packet / 'public/canonical.json')
            elif case == 'primary_pdf': append(next((packet / 'private/primary').glob('*.pdf')))
            elif case == 'copied_tree': append(packet / 'private/context/preprints-tree.json')
            elif case == 'history_body': append(next((packet / 'private/history').iterdir()))
            elif case == 'payload_symlink':
                target.unlink()
                target.symlink_to('report.md')
            elif case == 'payload_hardlink':
                target.unlink()
                os.link(packet / 'public/report.md', target)
            elif case == 'payload_mode': target.chmod(0o600 if stat.S_IMODE(target.stat().st_mode) != 0o600 else 0o644)
            pre = snapshot(dest)
            proc = subprocess.run([sys.executable, '-B', str(packet / 'public/verify.py'),
                                   '--root', str(dest), '--tree', str(a.tree.absolute()),
                                   '--final-sha256', fh, '--report-sha256', rh],
                                  capture_output=True, text=True, timeout=40)
            unchanged = pre == snapshot(dest)
            expected = (proc.returncode == 0) if case == 'baseline' else (proc.returncode != 0 and 'FAIL:' in proc.stderr)
            results.append({'case': case, 'expected': expected, 'inputs_unchanged': unchanged,
                            'returncode': proc.returncode, 'stdout': proc.stdout.strip(),
                            'stderr': proc.stderr.strip()})
            shutil.rmtree(dest)
    finally:
        shutil.rmtree(scratch)
    after = snapshot(root)
    receipt = {'kind': 'INTEGRITY_CONTROLS_ONLY', 'detached_final_sha256': a.final_sha256,
               'detached_report_sha256': a.report_sha256, 'cases': results,
               'whole_original_unchanged': before == after,
               'original_before': before, 'original_after': after,
               'all_expected': all(r['expected'] and r['inputs_unchanged'] for r in results)}
    (root / 'integrity-results.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'cases': len(results), 'all_expected': receipt['all_expected'],
                      'whole_original_unchanged': before == after}))
    if not receipt['all_expected'] or before != after:
        sys.exit(1)


if __name__ == '__main__':
    main()
