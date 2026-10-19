#!/usr/bin/env python3
"""Parent artifact replay on a disposable full copy; no mathematical gate."""
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
    'FINAL.json': '4c3fb91824c181411bd1b283424d5cd4252b239a077822639b3bf92120deda41',
    'REPORT.md': '8f4e08ed8052e474bffd98d2f39e8bc8b7e23164c3ef57606796aef78bef38f5',
    'packet/MANIFEST.json': '22ececd365c529d885356c205fa355f3866b18d1bd3b5b7f6bc6fec7897dd655',
    'integrity-results.json': '10a7fb20602687e99387a078dab19226b8f58e2184d5e88494f4feb9a6a58a70',
}


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


def run(args):
    p = subprocess.run(args, capture_output=True, text=True)
    assert p.returncode == 0, p.stdout + p.stderr
    return json.loads(p.stdout)


def main():
    parent = Path(__file__).resolve().parent
    campaign = parent.parent
    author = campaign / 'fresh-arithmetic-discovery-r91'
    tree = campaign.parents[2] / 'sources/preprints-tree.json'
    assert sha(tree) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    before = snapshot(author)
    for name, value in ANCHORS.items():
        assert sha(author / name) == value, name
    options = ['--tree', str(tree), '--final-sha256', ANCHORS['FINAL.json'],
               '--report-sha256', ANCHORS['REPORT.md']]
    verification = run([sys.executable, '-B', str(author / 'packet/public/verify.py'), '--root', str(author)] + options)
    with tempfile.TemporaryDirectory(prefix='.replay-', dir=parent) as tmp:
        copy = Path(tmp) / 'author'
        shutil.copytree(author, copy)
        assert snapshot(copy) == before
        summary = run([sys.executable, '-B', str(copy / 'packet/public/controls.py'), '--root', str(copy)] + options)
        receipt = json.loads((copy / 'integrity-results.json').read_text())
        assert summary['cases'] == 18 and summary['all_expected'] and summary['whole_original_unchanged']
        assert len(receipt['cases']) == 18 and all(x['expected'] and x['inputs_unchanged'] for x in receipt['cases'])
    assert snapshot(author) == before
    result = {'status': 'ARTIFACTS_ONLY', 'detached_anchors': ANCHORS, 'verification': verification,
              'controls': receipt, 'whole_actual_author_root_unchanged': True,
              'copy_runner_and_selected_verifiers_unmodified': True,
              'limits': '18 integrity cases only, mostly enclosing-seal rejections. Own per-case snapshot includes file bytes/modes/link counts and directory modes, not directory link counts. Parent separately compares every original file/directory mode/link count and file hash across the full replay. No audit-denial probes or hostile-code/race sandbox; no mathematical tests or gates.'}
    (parent / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'cases_expected': 18, 'whole_actual_author_root_unchanged': True, 'verification': verification}))


if __name__ == '__main__':
    main()
