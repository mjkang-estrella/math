#!/usr/bin/env python3
"""Disposable review-seal controls and whole-original preservation checks."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

SEAL = '247eb6e674ceb42d7c67aea58b3ff75f5a4159dd4670250a9e82eb9a26582219'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def snapshot(root):
    result = {}
    for p in [root] + sorted(root.rglob('*')):
        s = p.lstat()
        value = [s.st_mode, s.st_nlink]
        if stat.S_ISREG(s.st_mode):
            value += [s.st_size, sha(p)]
        elif stat.S_ISLNK(s.st_mode):
            value += [os.readlink(p)]
        result[p.relative_to(root).as_posix()] = value
    return result


def main():
    parent = Path(__file__).resolve().parent
    review = parent.parent / 't238b125-contribution-r1'
    author = parent.parent / 'fresh-structural-discovery-r125'
    before = {'review': snapshot(review), 'author': snapshot(author)}
    def verify(root, anchor=SEAL):
        return subprocess.run([sys.executable, '-B', str(parent / 'verify_contribution_r1.py'),
                               '--root', str(root), '--seal-sha256', anchor], capture_output=True, text=True)
    initial = verify(review)
    assert initial.returncode == 0, initial.stderr
    seal = json.loads((review / 'SEAL.json').read_text())
    paths = {'FINAL.json': 'FINAL.json', 'REPORT.md': 'REPORT.md',
             'MANIFEST.json': 'packet/MANIFEST.json', 'copied-controls/receipt.json': 'copied-controls/receipt.json',
             'proof.md': 'packet/public/proof.md', 'FROZEN-SCOPE.md': 'packet/public/FROZEN-SCOPE.md'}
    for name, rel in paths.items():
        assert sha(author / rel) == seal['author_detached_anchors_verified'][name], name
    author_check = subprocess.run([sys.executable, '-B', str(author / 'packet/public/verify.py'),
                                  '--root', str(author), '--finalhash', seal['author_detached_anchors_verified']['FINAL.json'],
                                  '--reporthash', seal['author_detached_anchors_verified']['REPORT.md']], capture_output=True, text=True)
    assert author_check.returncode == 0, author_check.stdout + author_check.stderr
    results = []
    cases = [('baseline', ''), ('wrong-seal', 'DETACHED_SEAL_HASH'),
             ('review-change', 'PAYLOAD_HASH:review.md'), ('seal-change', 'DETACHED_SEAL_HASH'),
             ('extra-file', 'EXACT_INVENTORY'), ('coherent-reseal-old-anchor', 'DETACHED_SEAL_HASH')]
    with tempfile.TemporaryDirectory(prefix='.contribution-r1-', dir=parent) as tmp:
        for name, reason in cases:
            root = Path(tmp) / name
            shutil.copytree(review, root)
            root.chmod(0o700)
            anchor = SEAL
            if name == 'wrong-seal':
                anchor = '0' * 64
            if name in {'review-change', 'coherent-reseal-old-anchor'}:
                p = root / 'review.md'; p.chmod(0o600); p.write_bytes(p.read_bytes() + b'\nMUTATION\n')
            if name == 'seal-change':
                p = root / 'SEAL.json'; p.chmod(0o600); p.write_bytes(p.read_bytes() + b'\n')
            if name == 'extra-file':
                (root / 'extra').write_text('extra')
            if name == 'coherent-reseal-old-anchor':
                p = root / 'SEAL.json'; p.chmod(0o600); s = json.loads(p.read_text())
                s['files']['review.md'] = sha(root / 'review.md'); p.write_text(json.dumps(s))
            copied_before = snapshot(root)
            run = verify(root, anchor)
            unchanged = snapshot(root) == copied_before
            expected = run.returncode == 0 if name == 'baseline' else run.returncode != 0 and reason in run.stderr
            assert expected and unchanged, (name, run.stdout, run.stderr)
            results.append({'case': name, 'expected': expected, 'copied_inputs_unchanged': unchanged,
                            'returncode': run.returncode, 'stdout': run.stdout.strip(), 'stderr': run.stderr.strip()})
    assert before == {'review': snapshot(review), 'author': snapshot(author)}
    result = {'status': 'ARTIFACTS_ONLY', 'detached_seal_sha256': SEAL,
              'verification': json.loads(initial.stdout), 'author_verification': json.loads(author_check.stdout),
              'all_six_author_anchors_match': True, 'cases': results,
              'whole_actual_review_root_unchanged': True, 'whole_actual_author_root_unchanged': True,
              'mathematical_gate': False,
              'limits': 'Reviewer supplied SEAL only, without requested own verifier/controls code. Parent supplementary verifier checks exact three-file membership, detached bytes and regular single links; SEAL does not bind modes. No hostile-code/race guarantee or isolated semantic parser tests.'}
    (parent / 'contribution-r1-replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'cases_expected': len(results), 'review_and_author_unchanged': True, 'status': 'ARTIFACTS_ONLY'}))


if __name__ == '__main__':
    main()
