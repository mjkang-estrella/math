#!/usr/bin/env python3
"""Copied adversarial controls for the review packet seal. MIT.

Never touches the original packet: each case copies it into the supplied
--scratch directory (which must lie outside the packet or be excluded from
the copy), mutates the copy, and runs the copied review-verify.py.
"""
import argparse, hashlib, json, os, shutil, subprocess, sys
from pathlib import Path


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


CASES = ['positive', 'wrong_manifest', 'wrong_verifier', 'edit_review', 'delete_review',
         'extra_file', 'extra_empty_dir', 'nested_manifest', 'root_symlink', 'ancestor_symlink',
         'payload_symlink', 'hardlink', 'fifo', 'edit_manifest', 'edit_verifier', 'self_reseal']


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--packet', required=True)
    ap.add_argument('--scratch', required=True)
    ap.add_argument('--expected-manifest', required=True)
    ap.add_argument('--expected-verifier', required=True)
    a = ap.parse_args()
    src = Path(a.packet).resolve()
    scratch = Path(a.scratch).resolve()
    results = {}
    for name in CASES:
        for child in list(scratch.iterdir()):
            if child.is_symlink() or not child.is_dir():
                child.unlink()
            else:
                shutil.rmtree(child)
        c = scratch / 'copy'
        shutil.copytree(src, c, ignore=lambda d, n: [scratch.name] if Path(d) == src else [])
        mh, vh = a.expected_manifest, a.expected_verifier
        script = c / 'review-verify.py'
        root = c
        if name == 'wrong_manifest':
            mh = '0' * 64
        if name == 'wrong_verifier':
            vh = '0' * 64
        if name == 'edit_review':
            with (c / 'review.md').open('a') as f:
                f.write('\nmutation\n')
        if name == 'delete_review':
            (c / 'review.md').unlink()
        if name == 'extra_file':
            (c / 'extra.txt').write_text('extra')
        if name == 'extra_empty_dir':
            (c / 'empty').mkdir()
        if name == 'nested_manifest':
            (c / 'nested').mkdir()
            (c / 'nested/manifest.json').write_text('{}')
        if name == 'root_symlink':
            os.symlink(c, scratch / 'rootlink')
            root = scratch / 'rootlink'
        if name == 'ancestor_symlink':
            (scratch / 'real').mkdir()
            shutil.move(str(c), scratch / 'real' / 'copy')
            os.symlink(scratch / 'real', scratch / 'anc')
            root = scratch / 'anc' / 'copy'
            script = root / 'review-verify.py'
        if name == 'payload_symlink':
            os.symlink('review.md', c / 'link.md')
        if name == 'hardlink':
            os.link(c / 'review.md', c / 'review-hardlink.md')
        if name == 'fifo':
            os.mkfifo(c / 'fifo')
        if name == 'edit_manifest':
            with (c / 'manifest.json').open('a') as f:
                f.write(' ')
        if name == 'edit_verifier':
            with (c / 'review-verify.py').open('a') as f:
                f.write('\n# mutation\n')
        if name == 'self_reseal':
            p = c / 'review.md'
            p.write_text(p.read_text().replace('PASS_FULL_T259S', 'FAIL', 1))
            m = json.loads((c / 'manifest.json').read_text())
            m['files']['review.md'] = {'bytes': p.stat().st_size, 'sha256': sha(p)}
            (c / 'manifest.json').write_text(json.dumps(m, sort_keys=True, indent=2) + '\n')
        cmd = [sys.executable, str(script), '--root', str(root),
               '--expected-manifest', mh, '--expected-verifier', vh]
        run = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
        ok = run.returncode == 0 if name == 'positive' else run.returncode != 0
        msg = (run.stdout + run.stderr).strip().split('\n')[-1][:120]
        results[name] = {'control': 'PASS' if ok else 'FAILED', 'returncode': run.returncode,
                         'message': msg if name == 'positive' else msg.split(':')[0] + ': ' + msg.split(':')[1].strip()
                         if ':' in msg else msg}
    for child in list(scratch.iterdir()):
        if child.is_symlink() or not child.is_dir():
            child.unlink()
        else:
            shutil.rmtree(child)
    status = 'PASS_ALL_REVIEW_CONTROLS' if all(r['control'] == 'PASS' for r in results.values()) else 'CONTROL_FAILURE'
    print(json.dumps({'status': status, 'cases': results}, sort_keys=True, indent=2))
    sys.exit(0 if status.startswith('PASS') else 1)


if __name__ == '__main__':
    main()
