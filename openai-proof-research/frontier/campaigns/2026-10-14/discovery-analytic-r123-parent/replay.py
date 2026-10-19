#!/usr/bin/env python3
"""Parent integrity replay adapted from analytic r122. MIT. No math gate."""
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
AUTHOR = HERE.parent / 'fresh-analytic-discovery-r123'
FINAL = 'c3b96217c912e7480bd848398e330332a1e3c7833cb13decf5dab8bd0c26f3ca'
REPORT = 'ac7d2eedb7ed0b45b59c0027c3b85945b196bcc26be7bb93ba2b8f8fd59907c0'
MANIFEST = 'ed3aee357620cad3798a54949b7f0e128e45472b5f6f80a46036792e7698b460'
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
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    row = {'command': list(map(str, cmd)), 'returncode': p.returncode,
           'stdout': p.stdout, 'stderr': p.stderr}
    assert p.returncode == 0, row
    return row


def main():
    before = inventory(AUTHOR)
    hashes = {'FINAL.json': FINAL, 'packet/public/report.md': REPORT,
              'MANIFEST.json': MANIFEST}
    assert all(sha((AUTHOR / n).read_bytes()) == h for n, h in hashes.items())
    treepath = REPO / 'sources/preprints-tree.json'
    tb = treepath.read_bytes()
    assert sha(tb) == TREE
    tree = json.loads(tb)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    canonical = {e['path']: e for e in tree['tree']}
    assert len(canonical) == 13223
    sources = json.loads((AUTHOR / 'packet/public/source-register.json').read_text())
    assert len(sources) == 12 and len({e['path'] for e in sources}) == 12
    for s in sources:
        e = canonical[s['path']]
        assert e['type'] == 'blob' and e['sha'] == s['blob'] and e['size'] == s['size']
        assert s['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + s['path']
    save('canonical-replay.json', {
        'scope': 'INTEGRITY_ONLY', 'tree_sha256': TREE, 'entries': 13223,
        'truncated': False, 'source_records': 12,
        'path_type_blob_size_pinned_raw_url_matched': True,
        'external_hashes_matched': hashes, 'mathematical_gate': False})
    common = ['--tree', str(treepath), '--finalhash', FINAL, '--reporthash', REPORT]
    save('integrity-replay.json', run([
        sys.executable, '-I', '-B', str(AUTHOR / 'packet/public/verify.py'),
        str(AUTHOR), *common]))
    with tempfile.TemporaryDirectory(prefix='copied-controls-', dir=HERE) as temp:
        copy = Path(temp) / 'author-copy'
        shutil.copytree(AUTHOR, copy, symlinks=True)
        out = copy / 'scratch/parent-replay-controls'
        assert not out.exists() and out.parent.is_dir()
        result = run([
            sys.executable, '-I', '-B', str(copy / 'packet/public/controls.py'),
            str(copy), '--out', str(out), *common])
        receipt = json.loads((out / 'receipt.json').read_text())
        cases = receipt['cases']
        assert len(cases) == 23 and len({c['case'] for c in cases}) == 23
        assert all(c['expected_outcome'] and c['copy_unchanged_by_verifier'] for c in cases)
        assert sum(c['returncode'] == 0 for c in cases) == 1
        assert next(c for c in cases if c['case'] == 'baseline')['returncode'] == 0
        for c in cases:
            if c['case'].endswith('denial-probe'):
                assert c['returncode'] != 0 and 'verifier denies' in c['stderr']
        assert receipt['all_expected'] and receipt['original_preexisting_tree_unchanged']
        save('copied-controls-replay.json', {
            'invocation': result, 'receipt': receipt,
            'fresh_output_only_on_disposable_copy': True,
            'original_author_control_receipt_preserved': True})
    after = inventory(AUTHOR)
    assert before == after
    save('author-unchanged.json', {
        'scope': 'INTEGRITY_ONLY', 'entire_author_root_unchanged': True,
        'before': before, 'after': after, 'copied_temporary_directories_removed': True})
    print(json.dumps({'integrity': 'PASS', 'canonical_sources': 12,
                      'copied_controls': 23, 'author_unchanged': True,
                      'mathematical_gate': False}))


if __name__ == '__main__':
    main()
