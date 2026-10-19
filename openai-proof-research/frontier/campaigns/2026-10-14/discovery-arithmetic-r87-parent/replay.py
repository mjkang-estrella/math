#!/usr/bin/env python3
"""Parent authentication and disposable integrity controls. MIT. No math gate."""
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
AUTHOR = HERE.parent / 'fresh-arithmetic-discovery-r87'
FINAL = 'ea8645da6d66e258cbea0dcca28307fa8a1e8e9df563185dcf171cce814005cb'
REPORT = '8f07f38eaf13d60ec4de95344fbc7b5b734379aead65838e8e78d8d04c986a3a'
MANIFEST = 'db7503f6b410e33c822b6cd5c240c0bf42da2162b62c611f803f9b9a2dcd6e5f'
PUBLIC = 'd223f511f7e1f7bf92fc3155d7d17d658ef6f46d8f56d511aab0ce8b57eaa65d'
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
    hashes = {'FINAL.json': FINAL, 'REPORT.md': REPORT, 'MANIFEST.json': MANIFEST,
              'packet/public/report.md': PUBLIC}
    assert all(sha((AUTHOR / n).read_bytes()) == h for n, h in hashes.items())
    treepath = REPO / 'sources/preprints-tree.json'
    tb = treepath.read_bytes()
    assert sha(tb) == TREE
    assert (AUTHOR / 'packet/private/context/preprints-tree.json').read_bytes() == tb
    tree = json.loads(tb)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    canonical = {e['path']: e for e in tree['tree']}
    assert len(canonical) == 13223
    sources = json.loads((AUTHOR / 'packet/public/source-register.json').read_text())
    assert len(sources) == 22 and len({e['path'] for e in sources}) == 22
    for s in sources:
        e = canonical[s['path']]
        assert e == s['canonical_record']
        assert e['type'] == 'blob' and e['sha'] == s['blob'] and e['size'] == s['bytes']
        assert s['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + s['path']
    save('canonical-replay.json', {
        'scope': 'INTEGRITY_ONLY', 'tree_sha256': TREE, 'entries': 13223,
        'truncated': False, 'source_records': 22,
        'full_canonical_record_path_type_blob_size_pinned_raw_url_matched': True,
        'external_hashes_matched': hashes, 'mathematical_gate': False})
    common = ['--finalhash', FINAL, '--reporthash', REPORT, '--tree', str(treepath)]
    save('integrity-replay.json', run([
        sys.executable, '-I', '-B', str(AUTHOR / 'verify.py'), str(AUTHOR), *common]))
    with tempfile.TemporaryDirectory(prefix='copied-controls-', dir=HERE) as temp:
        copy = Path(temp) / 'author-copy'
        shutil.copytree(AUTHOR, copy, symlinks=True)
        # The runner refuses prior output; remove ONLY the disposable copy's controls.
        shutil.rmtree(copy / 'controls')
        result = run([
            sys.executable, '-I', '-B', str(copy / 'run_controls.py'),
            str(copy), *common])
        receipt = json.loads((copy / 'controls/receipt.json').read_text())
        cases = receipt['cases']
        assert len(cases) == receipt['case_count'] == 20
        assert len({c['case'] for c in cases}) == 20
        assert all(c['matched'] and c['copied_inputs_unchanged'] for c in cases)
        assert sum(c['returncode'] == 0 for c in cases) == 1
        assert next(c for c in cases if c['case'] == 'baseline')['returncode'] == 0
        assert receipt['original_root_unchanged_except_controls_output']
        for c in cases:
            assert c['expected_diagnostic'] in c['stdout'] + c['stderr']
        save('copied-controls-replay.json', {
            'invocation': result, 'receipt': receipt,
            'removed_only_disposable_copy_prior_controls': True,
            'original_author_controls_and_snapshots_preserved': True})
    after = inventory(AUTHOR)
    assert before == after
    save('author-unchanged.json', {
        'scope': 'INTEGRITY_ONLY', 'entire_author_root_unchanged': True,
        'before': before, 'after': after, 'copied_temporary_directories_removed': True})
    print(json.dumps({'integrity': 'PASS', 'canonical_sources': 22,
                      'copied_controls': 20, 'author_unchanged': True,
                      'mathematical_gate': False}))


if __name__ == '__main__':
    main()
