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
AUTHOR = HERE.parent / 'fresh-arithmetic-discovery-r88'
FINAL = '757718c9a5f1af5f23da8c49693eea320c0a6d1f0e0dbaccdae6443c9d986b5e'
REPORT = '3c20bca5ebc2403a9f4c7ed552518c39a4d53f72973755d9dfb2f445c2183d2b'
MANIFEST = '5cf3ae0da5edce63af5a7fc8d11626bca0939a0d58f27c76e44488fbc522829d'
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
              'MANIFEST.json': MANIFEST}
    assert all(sha((AUTHOR / n).read_bytes()) == h for n, h in hashes.items())
    tb = (REPO / 'sources/preprints-tree.json').read_bytes()
    assert sha(tb) == TREE
    assert (AUTHOR / 'packet/private/context/preprints-tree.json').read_bytes() == tb
    tree = json.loads(tb)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    canonical = {e['path']: e for e in tree['tree']}
    assert len(canonical) == 13223
    sources = json.loads((AUTHOR / 'packet/private/acquisition.json').read_text())
    assert len(sources) == 85
    assert len({s['canonical']['path'] for s in sources}) == 85
    assert sum(s['retained'] is True for s in sources) == 16
    assert sum(s['retained'] is False for s in sources) == 69
    for s in sources:
        e = s['canonical']
        assert e == canonical[e['path']] and e['type'] == 'blob'
        assert s['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + e['path']
    save('canonical-replay.json', {
        'scope': 'INTEGRITY_ONLY', 'tree_sha256': TREE, 'entries': 13223,
        'truncated': False, 'source_records': 85, 'retained': 16, 'removed': 69,
        'all_full_canonical_records_and_pinned_raw_urls_matched': True,
        'removed_bodies_not_rehashed': True, 'external_hashes_matched': hashes,
        'mathematical_gate': False})
    common = ['--finalhash', FINAL, '--reporthash', REPORT]
    save('integrity-replay.json', run([
        sys.executable, '-I', '-B', str(AUTHOR / 'verify.py'), '--root', str(AUTHOR), *common, '--tree', str(REPO / 'sources/preprints-tree.json')]))
    with tempfile.TemporaryDirectory(prefix='copied-controls-', dir=HERE) as temp:
        copy = Path(temp) / 'author-copy'
        shutil.copytree(AUTHOR, copy, symlinks=True)
        out = copy / 'parent-replay-controls'
        assert not out.exists()
        result = run([
            sys.executable, '-I', '-B', str(copy / 'run_controls.py'),
            '--root', str(copy), '--out', str(out), *common])
        receipt = json.loads((out / 'receipt.json').read_text())
        cases = receipt['cases']
        assert len(cases) == 20
        assert len({c['case'] for c in cases}) == 20
        assert all(c['expected_outcome'] and c['copied_inputs_unchanged'] for c in cases)
        assert sum(c['returncode'] == 0 for c in cases) == 1
        assert next(c for c in cases if c['case'] == 'baseline')['returncode'] == 0
        assert receipt['original_preexisting_tree_unchanged']
        save('copied-controls-replay.json', {
            'invocation': result, 'receipt': receipt,
            'fresh_output_only_on_disposable_copy': True,
            'original_author_controls_preserved': True})
    after = inventory(AUTHOR)
    assert before == after
    save('author-unchanged.json', {
        'scope': 'INTEGRITY_ONLY', 'entire_author_root_unchanged': True,
        'before': before, 'after': after, 'copied_temporary_directories_removed': True})
    print(json.dumps({'integrity': 'PASS', 'canonical_records': 85, 'retained_sources': 16,
                      'copied_controls': 20, 'author_unchanged': True,
                      'mathematical_gate': False}))


if __name__ == '__main__':
    main()
