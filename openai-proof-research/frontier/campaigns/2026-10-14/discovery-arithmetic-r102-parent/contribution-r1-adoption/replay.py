#!/usr/bin/env python3
"""Authenticate full-scope contribution disposition; artifact checks only."""
import hashlib
import json
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[4]
BASE = PROJECT / 'frontier/campaigns/2026-10-14'
ROOT = BASE / 't009p102-contribution-r1'
AUTHOR = BASE / 'fresh-arithmetic-discovery-r102'
ANCHORS = {
    'final': '6720e762c5c0bfda83d1dde34d1c354888a163ac592f8ac242de5f43d2731736',
    'manifest': '47ae839c671f4053a166a81a2e2f8e1922aab7cc2c72f0982d63e64d13ecdf64',
    'report': 'f22d2c774412e7140b837836d5e190ec04ba8b8671fbf28babd7eaed573267ee',
}
AUTHOR_ANCHORS = {
    'final': 'eb35ddaa80501311da50e8f65d67dc33c970530e3b00003188182b2f8ef9e34f',
    'manifest': 'e212b8f45f7fb8ae07e30ba292ea8bab83c8983c0d3311f2bd308c0a590f8a9f',
    'report': '9d5253a754956107d1920df6d67353a1169ad54b5d7f7d5bc40d7331fe35c8c2',
}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def record(p):
    s = p.lstat()
    return {'mode': s.st_mode, 'nlink': s.st_nlink, 'size': s.st_size,
            'sha256': sha(p) if stat.S_ISREG(s.st_mode) else None}


def snap(root):
    return {str(p.relative_to(root)): record(p) for p in root.rglob('*')}


def run(args):
    p = subprocess.run(args, text=True, capture_output=True)
    assert p.returncode == 0, (args, p.returncode, p.stderr)
    return {'exit': p.returncode, 'stdout': p.stdout, 'stderr': p.stderr}


def verify(root, verifier, anchors):
    args = [sys.executable, '-B', str(verifier), '--root', str(root)]
    for k, v in anchors.items():
        args += ['--' + k + '-sha256', v]
    return run(args)


def main():
    before = {str(r): snap(r) for r in (ROOT, AUTHOR)}
    old = json.loads((ROOT / 'private/original-before.json').read_text())
    assert len(old) == 109 and old == json.loads((ROOT / 'private/original-after.json').read_text())
    assert snap(AUTHOR) == old
    named = json.loads((ROOT / 'private/external-originals-before.json').read_text())
    stable = [r for r in named if r['original'] != 'frontier/NEW-TEN-2026-10-14.md']
    assert len(stable) == 13 and len(named) == 14
    original_records = {r['original']: record(PROJECT / r['original']) for r in named}
    for r in stable:
        assert original_records[r['original']]['sha256'] == r['acquired_sha256'] == r['current_sha256']
    history = json.loads((ROOT / 'private/r73-receipt.json').read_text())
    assert sha(PROJECT / history['original']) == history['sha256'] == sha(ROOT / 'private/r73-reading-and-credit.md')
    history_before = record(PROJECT / history['original'])
    result = {'kind': 'PARENT_CONTRIBUTION_REVIEW_ADOPTION_ARTIFACT_REPLAY', 'anchors': ANCHORS,
              'review_verification': verify(ROOT, ROOT / 'verify.py', ANCHORS),
              'author_original_verification': verify(AUTHOR, AUTHOR / 'verify.py', AUTHOR_ANCHORS),
              'retained_author_copy_verification': verify(ROOT / 'private/author-copy', AUTHOR / 'verify.py', AUTHOR_ANCHORS)}
    assert sha(ROOT / 'public/SCOPE.md') == sha(AUTHOR / 'public/SCOPE.md')
    primary = json.loads((ROOT / 'private/primary/acquisition.json').read_text())
    assert sha(ROOT / 'private/primary/seshadri-1958-59.pdf') == primary['sha256']
    assert sha(ROOT / 'private/primary/seshadri-1958-59.txt') == primary['text_sha256']
    with tempfile.TemporaryDirectory(prefix='copy-', dir=HERE) as td:
        copy = Path(td) / 'review'
        shutil.copytree(ROOT, copy)
        result['copied_controls'] = run([sys.executable, '-B', str(copy / 'scratch/copied_controls.py')])
        receipt = json.loads((copy / 'controls/results.json').read_text())
        cases = receipt['cases']
        assert len(cases) == 9 and all(c['expected_accept'] == c['actual_accept'] for c in cases)
        assert [c['case'] for c in cases] == ['clean', 'prose-byte', 'missing-evidence', 'unexpected-hidden',
            'symlink', 'mode', 'outside-report', 'wrong-final', 'forged-reseal']
        result['control_cases'] = cases
    result['after_controls_review_verification'] = verify(ROOT, ROOT / 'verify.py', ANCHORS)
    assert all(record(PROJECT / rel) == r for rel, r in original_records.items())
    assert record(PROJECT / history['original']) == history_before
    unchanged = {str(r.relative_to(PROJECT)): snap(r) == before[str(r)] for r in (ROOT, AUTHOR)}
    assert all(unchanged.values())
    result.update(all_expected=True, review_payloads=126, review_directories=29, copied_cases=9,
                  author_payloads=85, author_directories=21, author_preservation_entries=109,
                  source_blobs=27, stable_named_originals_unchanged=13, additional_r73_original_unchanged=True,
                  mutable_ledger_observations=1, whole_actual_roots_unchanged=unchanged,
                  contribution='TECHNICAL_CONDITIONAL_ON_CORRECTNESS', correctness='UNREVIEWED',
                  accepted=False, count_change=0)
    result['limits'] = (
        'Full126-payload/29directory review root,exact author original/copy85payloads/21dirs and27 pinned blobs authenticate. '
        '109 recorded author file/directory entries match current original;13 stable named originals plus one additional '
        'r73 history file match,one mutable ledger excluded from acquired-identity claim. Whole current actual author/review '
        'roots and all named current files unchanged during replay;not historical whole-parent preservation or semantic '
        'reading of every private body. Nine unmodified supplied SMALL preseal-style fixtures check expected exit behavior; '
        'no independent per-fixture syscall/failure-reason audit or full-payload fixture claim. Disposable copied runner '
        'rewrites its own receipt after preservation check;no unchanged final seal of that disposable copy is claimed. '
        'No mathematical tests or independent correctness gate. Parent adopts only full-scope contribution TECHNICAL, '
        'conditional on correctness,with all reading/search/primary/chronology/traversal limits retained.')
    (HERE / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('all_expected', 'review_payloads', 'review_directories', 'author_payloads',
        'stable_named_originals_unchanged', 'additional_r73_original_unchanged', 'copied_cases', 'contribution', 'correctness')}))


if __name__ == '__main__':
    main()
