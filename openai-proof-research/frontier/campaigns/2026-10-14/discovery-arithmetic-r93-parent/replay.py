#!/usr/bin/env python3
"""Detached full-candidate evidence authentication and copied artifact controls."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

FINAL = '362dfe44e0db3abcddf9ce56f2a86f496e1e9c47297bf85c6e922847e760c479'
REPORT = '761a6e493e18f753c1f74902b3fade0a40ef12e34ec2dbb4474863c4d1b1dbe9'
MANIFEST = '8464240a224199d82189adc4681d9e2a4e64a74495e22f46201ce37efdc782e5'
FROZEN = 'ac626f4ab8d04589a8709854b9407f4577b72cdada161e6fe5f7943b7fa87572'
PROOF = 'b05e2ea21ed2d31c1521e9ef32c38358c335c1beb6278459834adab9c864ebf2'
CONTROLS = '759b2467a1db4ae1ee793409e595ec88519d0e2b4c71cae5123675a158cd0f5e'
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def snapshot(root):
    result = {}
    for p in [root, *sorted(root.rglob('*'))]:
        s = p.lstat(); value = [s.st_mode, s.st_nlink]
        if stat.S_ISREG(s.st_mode): value += [s.st_size, sha(p)]
        elif stat.S_ISLNK(s.st_mode): value += [os.readlink(p)]
        result[p.relative_to(root).as_posix()] = value
    return result


def run(args):
    r = subprocess.run(args, capture_output=True, text=True,
                       env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    assert r.returncode == 0, r.stdout + r.stderr
    return json.loads(r.stdout)


def main():
    parent = Path(__file__).resolve().parent
    author = parent.parent / 'fresh-arithmetic-discovery-r93'
    tree = author.parents[3] / 'sources/preprints-tree.json'
    anchors = {'FINAL.json': FINAL, 'REPORT.md': REPORT, 'packet/MANIFEST.json': MANIFEST,
               'packet/public/FROZEN.md': FROZEN, 'packet/public/proof.md': PROOF,
               'CONTROLS.json': CONTROLS}
    assert all(sha(author / path) == value for path, value in anchors.items())
    assert sha(tree) == TREE
    assert tree.read_bytes() == (author / 'packet/private/context/sources/preprints-tree.json').read_bytes()
    before = snapshot(author); tree_before = [tree.stat().st_mode, tree.stat().st_nlink, sha(tree)]
    options = ['--final-sha256', FINAL]
    verification = run([sys.executable, '-B', str(author / 'packet/public/code/verify.py'),
                        '--root', str(author), *options])
    with tempfile.TemporaryDirectory(prefix='.replay-', dir=parent) as tmp:
        copy = Path(tmp) / 'author'; shutil.copytree(author, copy)
        assert snapshot(copy) == before
        receipt = run([sys.executable, '-B', str(copy / 'packet/public/code/controls.py'),
                       '--root', str(copy), *options])
        assert len(receipt['cases']) == 14 and receipt['all_expected']
        assert receipt['whole_actual_author_root_unchanged']
        assert all(x['expected_outcome'] and x['copied_inputs_unchanged'] for x in receipt['cases'])
        assert snapshot(copy) == before
    assert snapshot(author) == before
    assert [tree.stat().st_mode, tree.stat().st_nlink, sha(tree)] == tree_before
    result = {'status': 'ARTIFACTS_ONLY', 'detached_anchors': anchors,
              'verification': verification, 'controls': receipt,
              'whole_actual_author_root_unchanged': True, 'whole_copied_author_root_unchanged': True,
              'external_canonical_tree_matches_and_unchanged': True,
              'selected_manifest_bound_runner_and_verifiers_unmodified': True,
              'limits': '14 artifact cases: baseline and13 rejections,3 deliberately newly anchored internal mutants. Full per-copy and full actual-root snapshots preserve paths/types/bytes/modes/link counts. Own audit hook denies specified writes/mutations/subprocesses; no explicit denial probes. Manifest mode and root extra-file inventory are not sealed; full preservation separately checked. No mathematical test/gate or hostile-runtime/race certification.'}
    (parent / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'cases_expected': 14, 'originals_unchanged': True, 'verification': verification}))


if __name__ == '__main__': main()
