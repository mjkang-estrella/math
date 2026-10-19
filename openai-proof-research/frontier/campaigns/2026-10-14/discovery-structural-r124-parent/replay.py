#!/usr/bin/env python3
"""Parent authentication and copied integrity controls. No mathematical gate."""
import hashlib
import json
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
AUTHOR = HERE.parent / 'fresh-structural-discovery-r124'
FINAL = 'd3ca6081ec4f90aaa52d68bf8658bba5a6ecdc16472c5f6d73ce6cc005b98880'
REPORT = 'ea313aff9a06d9838c57790caaf8afbe999c3d799d83efe4b109f787e555b494'
MANIFEST = 'f2e40ed4d75a1deaebe0ec1da25f2ba82ecc27c7eb7c55763f7cd6a9bd88d8e9'
PUBLIC = 'f68dc313291ebc65e4931e394ab390e51bcc125be538235fe80e6dde9767f98f'
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def save(name, data):
    (HERE / name).write_text(json.dumps(data, indent=2) + '\n')


def inventory(root):
    rows = {}
    for p in [root, *sorted(root.rglob('*'))]:
        s = p.lstat()
        row = {'mode': s.st_mode, 'nlink': s.st_nlink}
        if stat.S_ISREG(s.st_mode):
            row.update(bytes=s.st_size, sha256=sha(p.read_bytes()))
        else:
            assert stat.S_ISDIR(s.st_mode), str(p)
        rows[p.relative_to(root).as_posix()] = row
    return rows


def run(cmd):
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=150)
    row = {'command': list(map(str, cmd)), 'returncode': p.returncode,
           'stdout': p.stdout, 'stderr': p.stderr}
    assert p.returncode == 0, row
    return row


def main():
    before = inventory(AUTHOR)
    hashes = {'FINAL.json': FINAL, 'REPORT.md': REPORT,
              'packet/MANIFEST.json': MANIFEST, 'packet/public/report.md': PUBLIC}
    assert all(sha((AUTHOR / n).read_bytes()) == h for n, h in hashes.items())
    tb = (REPO / 'sources/preprints-tree.json').read_bytes()
    assert sha(tb) == TREE
    assert (AUTHOR / 'packet/private/context/sources/preprints-tree.json').read_bytes() == tb
    tree = json.loads(tb)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    canonical = {e['path']: e for e in tree['tree']}
    assert len(canonical) == 13223
    sources = json.loads((AUTHOR / 'packet/public/source-register.json').read_text())
    assert len(sources) == 61
    assert len({s['record']['path'] for s in sources}) == 61
    assert sum(s['retained'] is True for s in sources) == 18
    assert sum(s['retained'] is False for s in sources) == 43
    for s in sources:
        e = s['record']
        assert e == canonical[e['path']] and e['type'] == 'blob'
        assert s['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + e['path']
    save('canonical-replay.json', {
        'scope': 'INTEGRITY_ONLY', 'tree_sha256': TREE, 'entries': 13223,
        'truncated': False, 'source_records': 61, 'retained': 18, 'removed': 43,
        'all_full_canonical_records_and_pinned_raw_urls_matched': True,
        'removed_bodies_not_rehashed': True, 'external_hashes_matched': hashes,
        'mathematical_gate': False})
    common = ['--finalhash', FINAL, '--reporthash', REPORT]
    save('integrity-replay.json', run([
        sys.executable, '-I', '-B', str(AUTHOR / 'verify.py'), '--root', str(AUTHOR), *common]))
    with tempfile.TemporaryDirectory(prefix='copied-controls-', dir=HERE) as temp:
        copy = Path(temp) / 'author-copy'
        shutil.copytree(AUTHOR, copy, symlinks=True)
        out = copy / 'parent-replay-controls'
        assert not out.exists()
        result = run([
            sys.executable, '-I', '-B', str(copy / 'run_controls.py'),
            '--root', str(copy), '--output', str(out), *common])
        receipt = json.loads((out / 'receipt.json').read_text())
        cases = receipt['cases']
        assert len(cases) == receipt['case_count'] == 26
        assert len({c['case'] for c in cases}) == 26
        assert all(c['expected_result_observed'] and c['input_unchanged'] for c in cases)
        assert sum(c['returncode'] == 0 for c in cases) == 1
        assert next(c for c in cases if c['case'] == 'baseline')['returncode'] == 0
        assert sum(c['case'].startswith('NEW-TEST') for c in cases) == 6
        assert receipt['all_expected'] and receipt['original_unchanged']
        save('copied-controls-replay.json', {
            'invocation': result, 'receipt': receipt,
            'fresh_output_only_on_disposable_copy': True,
            'original_author_controls_preserved': True})
    after = inventory(AUTHOR)
    assert before == after
    save('author-unchanged.json', {
        'scope': 'INTEGRITY_ONLY', 'entire_author_root_unchanged': True,
        'before': before, 'after': after, 'copied_temporary_directories_removed': True})
    print(json.dumps({'integrity': 'PASS', 'canonical_records': 61, 'retained_sources': 18,
                      'copied_controls': 26, 'author_unchanged': True,
                      'mathematical_gate': False}))


if __name__ == '__main__':
    main()
