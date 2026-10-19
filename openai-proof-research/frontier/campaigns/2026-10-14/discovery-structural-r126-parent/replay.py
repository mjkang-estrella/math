#!/usr/bin/env python3
"""Detached archive verification and unchanged-runner copied integrity replay."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

FINAL = '66320e200ef32ff1374cf8b13c9a8717de09083d8b3b5d05281862986e5a2a65'
REPORT = '319b631afa0b3f44bb3d1e95010dce4cc050f34e4460d6fbc6e61a11dd1f679d'


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def snapshot(root):
    out = {}
    for p in [root] + sorted(root.rglob('*')):
        s = p.lstat(); value = [s.st_mode, s.st_nlink]
        if stat.S_ISREG(s.st_mode): value += [s.st_size, sha(p)]
        elif stat.S_ISLNK(s.st_mode): value += [os.readlink(p)]
        out[p.relative_to(root).as_posix()] = value
    return out


def run(args):
    r = subprocess.run(args, capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr
    return json.loads(r.stdout)


def main():
    parent = Path(__file__).resolve().parent; author = parent.parent / 'fresh-structural-discovery-r126'
    tree = parent.parent.parents[2] / 'sources/preprints-tree.json'
    assert sha(tree) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    assert sha(author / 'FINAL.json') == FINAL and sha(author / 'REPORT.md') == REPORT
    assert sha(author / 'packet/MANIFEST.json') == 'bec85a4ae60c0b7ef19a42c0496ce7de414855d00891b445b7c0b92e91ba5406'
    before = snapshot(author); tree_before = sha(tree)
    verification = run([sys.executable, '-B', str(author / 'packet/public/verify.py'),
                        '--packet', str(author / 'packet'), '--final', str(author / 'FINAL.json'),
                        '--final-sha256', FINAL, '--tree', str(tree)])
    with tempfile.TemporaryDirectory(prefix='.replay-', dir=parent) as tmp:
        copy = Path(tmp) / 'author'; shutil.copytree(author, copy)
        assert snapshot(copy) == before
        summary = run([sys.executable, '-B', str(copy / 'packet/public/controls.py'),
                       '--root', str(copy), '--tree', str(tree), '--final-sha256', FINAL])
        receipt = json.loads((copy / 'controls.json').read_text())
        assert summary['all_expected'] and summary['cases'] == 17 and summary['originals_unchanged']
        assert len(receipt['cases']) == 17 and all(x['copy_unchanged'] for x in receipt['cases'])
        assert all((x['exit'] == 0) == (x['case'] == 'baseline') for x in receipt['cases'])
    assert snapshot(author) == before and sha(tree) == tree_before
    result = {'status': 'ARTIFACTS_ONLY', 'detached_final_sha256': FINAL, 'detached_report_sha256': REPORT,
              'verification': verification, 'controls': receipt, 'whole_actual_author_root_unchanged': True,
              'external_canonical_tree_unchanged': True, 'copy_runner_and_selected_verifiers_unmodified': True,
              'limits': '17 artifact cases, including explicit reanchored metadata/report and two audit denials; no mathematical test or gate. Payload/directory modes sealed, manifest/outside FINAL modes not sealed; parent full-root snapshots compare all modes/link counts separately. Own controls preserve copied inputs, original packet/FINAL/tree; parent additionally preserves all actual outside report/scratch/receipt files. No hostile-code/race certification.'}
    (parent / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'cases_expected': 17, 'whole_actual_author_root_unchanged': True, 'verification': verification}))


if __name__ == '__main__': main()
