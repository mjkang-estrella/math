#!/usr/bin/env python3
"""Authenticate the detached proof-review seal and replay its copied controls."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

FINAL = '0f98d335de5c0dafbaf7bbae268e9c1ffb7506d78544d08b331915349718f213'
REPORT = 'c267e71537e6c1027c398bef42143729bdc24143eb43e0113b8622c6e6a4d5ec'
MANIFEST = '3ff5e10d80bfeff5cf7c9206156bbbaa11394aaff5e369b8fd6ffb6843cc8253'
AUTHOR = '362dfe44e0db3abcddf9ce56f2a86f496e1e9c47297bf85c6e922847e760c479'
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


def authenticate(review):
    assert sha(review / 'FINAL.json') == FINAL
    assert sha(review / 'REPORT.md') == REPORT
    assert sha(review / 'MANIFEST.json') == MANIFEST
    f = json.loads((review / 'FINAL.json').read_text())
    assert f['manifest_sha256'] == MANIFEST and f['report_sha256'] == REPORT
    assert f['author_final_sha256'] == AUTHOR
    assert f['verdict'] == 'PASS' and f['full_original_scope']
    assert not f['blocking_issues'] and not f['required_repairs']
    m = json.loads((review / 'MANIFEST.json').read_text())
    excluded = set(m['seal_files_excluded'])
    assert excluded == {'FINAL.json', 'MANIFEST.json'}
    files = {}; dirs = {}
    for p in [review, *sorted(review.rglob('*'))]:
        s = p.lstat(); k = p.relative_to(review).as_posix()
        assert not stat.S_ISLNK(s.st_mode)
        if stat.S_ISDIR(s.st_mode): dirs[k] = stat.S_IMODE(s.st_mode)
        else:
            assert stat.S_ISREG(s.st_mode) and s.st_nlink == 1
            if k not in excluded:
                files[k] = {'bytes': s.st_size, 'sha256': sha(p),
                            'mode': stat.S_IMODE(s.st_mode), 'nlink': s.st_nlink}
    assert files == m['files'] and dirs == m['directory_modes']
    return {'payloads': len(files), 'directories': len(dirs), 'exact_review_membership': True}


def run(args):
    r = subprocess.run(args, capture_output=True, text=True,
                       env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    assert r.returncode == 0, r.stdout + r.stderr
    return json.loads(r.stdout)


def main():
    parent = Path(__file__).resolve().parent
    author = parent.parent / 'fresh-arithmetic-discovery-r93'
    review = parent.parent / 't195d93-proof-r1'
    tree = author.parents[3] / 'sources/preprints-tree.json'
    seal = authenticate(review)
    assert sha(author / 'FINAL.json') == AUTHOR and sha(tree) == TREE
    before_author = snapshot(author); before_review = snapshot(review)
    before_tree = [tree.stat().st_mode, tree.stat().st_nlink, sha(tree)]
    verifier = review / 'public/code/verify.py'
    direct = run([sys.executable, '-B', str(verifier), '--root', str(author),
                  '--tree', str(tree), '--final-sha256', AUTHOR])
    with tempfile.TemporaryDirectory(prefix='.proof-r1-', dir=parent) as td:
        tmp = Path(td); campaign = tmp / 'frontier/campaigns/2026-10-14'
        author_copy = campaign / author.name; review_copy = campaign / review.name
        shutil.copytree(author, author_copy); shutil.copytree(review, review_copy)
        assert snapshot(author_copy) == before_author and snapshot(review_copy) == before_review
        (tmp / 'sources').mkdir(); shutil.copy2(tree, tmp / 'sources/preprints-tree.json')
        summary = run([sys.executable, '-B', str(review_copy / 'public/code/controls.py')])
        receipt = json.loads((review_copy / 'private/integrity.json').read_text())
        assert summary['cases'] == 14 and summary['all_expected']
        assert summary['whole_original_preserved'] and summary['external_tree_preserved']
        assert len(receipt['cases']) == 14
        assert all(x['expected'] and x['unchanged'] for x in receipt['cases'])
        assert snapshot(author_copy) == before_author
        changed_review = snapshot(review_copy)
        changed_review.pop('private/integrity.json')
        expected_review = dict(before_review); expected_review.pop('private/integrity.json')
        assert changed_review == expected_review
        assert sha(tmp / 'sources/preprints-tree.json') == TREE
        # Retain only parent observations, not copies of private reviewer receipts.
        cases = [{k: x[k] for k in ['case', 'expected', 'unchanged', 'returncode',
                                   'deliberate_new_test_anchor']} for x in receipt['cases']]
    assert snapshot(author) == before_author and snapshot(review) == before_review
    assert [tree.stat().st_mode, tree.stat().st_nlink, sha(tree)] == before_tree
    result = {'status': 'ARTIFACTS_ONLY', 'detached_review_final_sha256': FINAL,
              'detached_review_report_sha256': REPORT, 'review_seal': seal,
              'independent_author_verification': direct, 'cases': cases,
              'copied_cases_expected': 14, 'all_copied_inputs_unchanged': True,
              'whole_actual_author_root_unchanged': True, 'whole_actual_review_root_unchanged': True,
              'external_canonical_tree_unchanged': True,
              'selected_reviewer_runner_and_verifier_unmodified': True,
              'private_reviewer_receipts_not_copied_into_parent_public_records': True,
              'limits': '14 integrity cases only, plus direct original-author verification. Three deliberately reanchored copied internal mutants. Review seal binds exact payload names/bytes/modes/link counts and directories; two seal-file modes excluded. Author manifest mode/root extra-file inventory not sealed. Full actual and copied snapshots separately preserve these attributes; only the copied private integrity receipt is regenerated. No audit-denial probes, mathematical test/gate, hostile-runtime or race certification.'}
    (parent / 'proof-r1-replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'copied_cases_expected': 14, 'originals_unchanged': True,
                      'review_seal': seal, 'author_verification': direct}))


if __name__ == '__main__': main()
