#!/usr/bin/env python3
"""Integrity controls on disposable copies only; never a mathematical test.
Use --check-record after final sealing to replay without changing the receipt.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def snapshot(root, skip_work=False):
    rows = {}
    for base, dirs, files in os.walk(root, followlinks=False):
        if skip_work and Path(base) == root / 'private/work':
            dirs[:] = []
            files = []
        for name in dirs + files:
            p = Path(base) / name
            s = p.lstat()
            rows[p.relative_to(root).as_posix()] = [s.st_mode, s.st_nlink,
                os.readlink(p) if p.is_symlink() else sha(p) if p.is_file() else None]
    rows['.'] = [root.lstat().st_mode]
    return rows


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--review', type=Path, required=True)
    ap.add_argument('--reviewmanifest', required=True)
    ap.add_argument('--author', type=Path, required=True)
    ap.add_argument('--workspace', type=Path, required=True)
    ap.add_argument('--check-record', action='store_true')
    a = ap.parse_args()
    review, author, workspace = a.review.resolve(), a.author.resolve(), a.workspace.resolve()
    work = review / 'private/work'
    if any(work.iterdir()):
        raise ValueError('control workspace must be empty')
    original_review = snapshot(review, True)
    original_author = snapshot(author)
    cases = [
        ('copied-baseline', None),
        ('wrong-review-anchor', 'DETACHED manifest anchor mismatch'),
        ('missing-review-anchor', '--reviewmanifest'),
        ('changed-review', 'payload metadata/hash mismatch: review.md'),
        ('changed-reading-limits', 'payload metadata/hash mismatch: reading-limits.md'),
        ('changed-review-verifier', 'payload metadata/hash mismatch: public/verify.py'),
        ('changed-private-primary', 'payload metadata/hash mismatch: private/foreman-weiss-symbolic-v2.pdf'),
        ('missing-file', 'exact membership/directory metadata mismatch'),
        ('extra-file', 'exact membership/directory metadata mismatch'),
        ('extra-empty-directory', 'exact membership/directory metadata mismatch'),
        ('payload-symlink', 'symlink, hardlink or special member'),
        ('payload-hardlink', 'symlink, hardlink or special member'),
        ('root-symlink', 'root must be a real directory'),
        ('changed-file-mode', 'payload metadata/hash mismatch: review.md'),
        ('changed-root-mode', 'root/manifest mode mismatch'),
        ('changed-manifest-mode', 'root/manifest mode mismatch'),
        ('changed-manifest-bytes', 'DETACHED manifest anchor mismatch'),
        ('resealed-review-and-manifest', 'DETACHED manifest anchor mismatch'),
        ('changed-author-anchor-binding-resealed', 'DETACHED manifest anchor mismatch'),
        ('changed-author-manifest', 'AUTHOR handoff anchor mismatch: packet/manifest.json'),
        ('changed-author-FINAL', 'AUTHOR handoff anchor mismatch: FINAL.json'),
        ('changed-author-report', 'AUTHOR handoff anchor mismatch: packet/public/research-report.md'),
        ('changed-author-frozen', 'AUTHOR handoff anchor mismatch: packet/public/frozen-target.md'),
        ('changed-author-proof', 'AUTHOR handoff anchor mismatch: packet/public/proof.md'),
        ('changed-author-verifier', 'AUTHOR handoff anchor mismatch: packet/public/verify.py'),
        ('changed-author-source', 'payload metadata/hash mismatch: private/upstream/152/04-switching.tex'),
        ('changed-author-primary', 'payload metadata/hash mismatch: private/primary/katok-thouvenot1997.pdf'),
        ('changed-complete-tree', 'complete-tree anchor mismatch'),
    ]
    results = []
    for case, reason in cases:
        with tempfile.TemporaryDirectory(prefix='copy-control-', dir=work) as td:
            base = Path(td)
            cp, ca, ws = base / 'review', base / 'author', base / 'workspace'
            def ignore(path, names):
                return names if Path(path) == work else []
            shutil.copytree(review, cp, ignore=ignore)
            shutil.copytree(author, ca)
            (ws / 'sources').mkdir(parents=True)
            shutil.copy2(workspace / 'sources/preprints-tree.json', ws / 'sources/preprints-tree.json')
            target_review = cp
            changes = {
                'changed-review': cp / 'review.md',
                'changed-reading-limits': cp / 'reading-limits.md',
                'changed-review-verifier': cp / 'public/verify.py',
                'changed-private-primary': cp / 'private/foreman-weiss-symbolic-v2.pdf',
                'changed-author-manifest': ca / 'packet/manifest.json',
                'changed-author-FINAL': ca / 'FINAL.json',
                'changed-author-report': ca / 'packet/public/research-report.md',
                'changed-author-frozen': ca / 'packet/public/frozen-target.md',
                'changed-author-proof': ca / 'packet/public/proof.md',
                'changed-author-verifier': ca / 'packet/public/verify.py',
                'changed-author-source': ca / 'packet/private/upstream/152/04-switching.tex',
                'changed-author-primary': ca / 'packet/private/primary/katok-thouvenot1997.pdf',
                'changed-complete-tree': ws / 'sources/preprints-tree.json',
                'changed-manifest-bytes': cp / 'manifest.json',
            }
            if case in changes:
                p = changes[case]
                p.write_bytes(p.read_bytes() + b'\nmutation\n')
            if case == 'missing-file':
                (cp / 'review.md').unlink()
            if case == 'extra-file':
                (cp / 'extra').write_text('unexpected')
            if case == 'extra-empty-directory':
                (cp / 'extra-directory').mkdir()
            if case == 'payload-symlink':
                (cp / 'review.md').unlink()
                (cp / 'review.md').symlink_to('reading-limits.md')
            if case == 'payload-hardlink':
                (cp / 'review.md').unlink()
                os.link(cp / 'reading-limits.md', cp / 'review.md')
            if case == 'root-symlink':
                target_review = base / 'review-alias'
                target_review.symlink_to(cp, target_is_directory=True)
            if case == 'changed-file-mode':
                (cp / 'review.md').chmod(0o600)
            if case == 'changed-root-mode':
                cp.chmod(0o700)
            if case == 'changed-manifest-mode':
                (cp / 'manifest.json').chmod(0o600)
            if case in ('resealed-review-and-manifest', 'changed-author-anchor-binding-resealed'):
                mf = cp / 'manifest.json'
                m = json.loads(mf.read_text())
                if case == 'resealed-review-and-manifest':
                    p = cp / 'review.md'
                    p.write_bytes(p.read_bytes() + b'\nforged conclusion\n')
                    m['files']['review.md']['bytes'] = p.stat().st_size
                    m['files']['review.md']['sha256'] = sha(p)
                else:
                    m['author_anchors']['packet/public/proof.md'] = '0' * 64
                mf.write_text(json.dumps(m, sort_keys=True, indent=2) + '\n')
            cmd = [sys.executable, '-B', str(review / 'public/verify.py'),
                   '--review', str(target_review), '--author', str(ca), '--workspace', str(ws)]
            if case != 'missing-review-anchor':
                cmd += ['--reviewmanifest', '0' * 64 if case == 'wrong-review-anchor' else a.reviewmanifest]
            before = [snapshot(cp), snapshot(ca), snapshot(ws)]
            r = subprocess.run(cmd, text=True, capture_output=True)
            after = [snapshot(cp), snapshot(ca), snapshot(ws)]
            output = (r.stdout + r.stderr).strip()
            # argparse includes the trusted verifier path; normalize that one diagnostic.
            if case == 'missing-review-anchor':
                output = output.splitlines()[-1]
            ok = ((r.returncode == 0) == (reason is None)
                  and (reason is None or reason in output) and before == after)
            results.append({'case': case, 'expected_accept': reason is None,
                'expected_rejection_reason': reason, 'returncode': r.returncode,
                'actual_output': output, 'verifier_read_only': before == after,
                'control_passed': ok})
    unchanged = snapshot(review, True) == original_review and snapshot(author) == original_author
    record = {'schema': 't152ac116-copied-integrity-controls-v1',
              'review_anchor_origin': 'externally supplied at invocation; not derived as a trust anchor',
              'original_review_unchanged_during_verification': unchanged,
              'original_author_unchanged': snapshot(author) == original_author,
              'results': results, 'mathematical_gate': False, 'priority_gate': False}
    raw = json.dumps(record, sort_keys=True, indent=2) + '\n'
    receipt = review / 'public/integrity-controls.json'
    if a.check_record:
        if receipt.read_text() != raw:
            raise ValueError('final replay differs from sealed control receipt')
    else:
        receipt.write_text(raw)
    print(json.dumps({'controls': len(results), 'passed': sum(x['control_passed'] for x in results),
                      'originals_unchanged': unchanged, 'sealed_receipt_matched': a.check_record}, sort_keys=True))
    return 0 if unchanged and all(x['control_passed'] for x in results) else 1


if __name__ == '__main__':
    raise SystemExit(main())
