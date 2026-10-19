#!/usr/bin/env python3
"""Detached archive authentication and unchanged-runner copied replay."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

ANCHORS = {
    'FINAL.json': '31bf3210c971d9e418967eddc9a996431beae6e1eacbbd23ea71579891ce5f48',
    'REPORT.md': '4e7a4bfb32f0a90c9f725f335f696f197c4e307d635a451c69b8b7b1c2377b90',
    'packet/MANIFEST.json': 'a8883ebda7f513db2b4679a05a6be80ac7aa7648d08afe9969e878d913b81f1d',
    'integrity-results.json': '4dad0446fab7411983d48be3ee4a1238aac01e871701ba922de7fb1a45ec3d38',
}


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def snapshot(root):
    rows = {}
    for p in [root] + sorted(root.rglob('*')):
        s = p.lstat(); value = [s.st_mode, s.st_nlink]
        if stat.S_ISREG(s.st_mode): value += [s.st_size, sha(p)]
        elif stat.S_ISLNK(s.st_mode): value += [os.readlink(p)]
        rows[p.relative_to(root).as_posix()] = value
    return rows


def run(args):
    p = subprocess.run(args, capture_output=True, text=True)
    assert p.returncode == 0, p.stdout + p.stderr
    return json.loads(p.stdout)


def main():
    parent = Path(__file__).resolve().parent
    author = parent.parent / 'fresh-arithmetic-discovery-r92'
    tree = parent.parent.parents[2] / 'sources/preprints-tree.json'
    before = snapshot(author)
    for name, value in ANCHORS.items(): assert sha(author / name) == value, name
    assert sha(tree) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    options = ['--tree', str(tree), '--final-sha256', ANCHORS['FINAL.json'], '--report-sha256', ANCHORS['REPORT.md']]
    verification = run([sys.executable, '-B', str(author / 'packet/code/verify.py'), '--root', str(author)] + options)
    with tempfile.TemporaryDirectory(prefix='.replay-', dir=parent) as tmp:
        copy = Path(tmp) / 'author'; shutil.copytree(author, copy)
        assert snapshot(copy) == before
        summary = run([sys.executable, '-B', str(copy / 'packet/code/controls.py'), '--root', str(copy)] + options)
        receipt = json.loads((copy / 'integrity-results.json').read_text())
        assert summary['cases'] == 14 and summary['all_expected'] and summary['author_root_unchanged']
        assert len(receipt['cases']) == 14 and all(x['expected_result'] and x['copy_inputs_unchanged'] for x in receipt['cases'])
    assert snapshot(author) == before
    result = {'status': 'ARTIFACTS_ONLY', 'detached_anchors': ANCHORS, 'verification': verification,
              'controls': receipt, 'whole_actual_author_root_unchanged': True,
              'copy_runner_and_selected_verifiers_unmodified': True,
              'limits': '14 artifact cases under original detached anchors; no mathematical tests/gates, artificial reanchoring or audit-denial probes. Payload and directory modes sealed; outside FINAL/REPORT and manifest modes not sealed. Parent separately preserves whole actual original paths/bytes/modes/link counts including receipt and scratch. No hostile-code/race guarantee.'}
    (parent / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'cases_expected': 14, 'whole_actual_author_root_unchanged': True, 'verification': verification}))


if __name__ == '__main__': main()
