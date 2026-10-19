#!/usr/bin/env python3
"""Parent authentication, finite identity replay and copied integrity controls. MIT."""
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
AUTHOR = HERE.parent / 'fresh-structural-discovery-r123'
FINAL = '9138b1862ea2ec4da0590db16b624499c8598ecbdf8a099a5ad9369fd53cd4e8'
REPORT = 'af360fa670c4863b845ca353995cfcb53697955c822cc0690abdf7a071188b8f'
MANIFEST = '29aeb665dfff32718625c9823a50f4aeebbabb5046593880833a3c160633dfc5'
PUBLIC = 'c62527f78e70efe01ad968a52e2474541f2997afeecf5d6fc89b0c9c1a944b9b'
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
    tb = (REPO / 'sources/preprints-tree.json').read_bytes()
    assert sha(tb) == TREE
    assert (AUTHOR / 'packet/private/context/preprints-tree.json').read_bytes() == tb
    tree = json.loads(tb)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    canonical = {e['path']: e for e in tree['tree']}
    assert len(canonical) == 13223
    sources = json.loads((AUTHOR / 'packet/public/source-register.json').read_text())
    assert len(sources) == 21 and len({e['path'] for e in sources}) == 21
    for s in sources:
        e = canonical[s['path']]
        assert e == s['canonical_record']
        assert e['type'] == 'blob' and e['sha'] == s['git_blob'] and e['size'] == s['bytes']
        assert s['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + s['path']
    save('canonical-replay.json', {
        'scope': 'INTEGRITY_ONLY', 'tree_sha256': TREE, 'entries': 13223,
        'truncated': False, 'source_records': 21,
        'full_canonical_record_path_type_blob_size_pinned_raw_url_matched': True,
        'external_hashes_matched': hashes, 'mathematical_gate': False})
    common = ['--finalhash', FINAL, '--reporthash', REPORT]
    save('integrity-replay.json', run([
        sys.executable, '-I', '-B', str(AUTHOR / 'verify.py'),
        '--root', str(AUTHOR), *common]))
    algebra = run([sys.executable, '-I', '-B', str(AUTHOR / 'packet/public/algebra-check.py')])
    assert json.loads(algebra['stdout']) == json.loads(
        (AUTHOR / 'packet/public/algebra-check.json').read_text())
    save('algebra-replay.json', {
        'invocation': algebra, 'author_receipt_matched': True,
        'scope': 'ONE_FINITE_POLYNOMIAL_COEFFICIENT_IDENTITY',
        'mathematical_gate': False})
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
        assert len(cases) == 23 and len({c['name'] for c in cases}) == 23
        assert all(c['expected_result'] and c['copied_input_unchanged'] for c in cases)
        assert sum(c['returncode'] == 0 for c in cases) == 3
        for c in cases:
            if c['name'] in ['deny-write', 'deny-process']:
                assert json.loads(c['stdout']) == {
                    'probe': c['name'].removeprefix('deny-'), 'denied': True}
        assert receipt['all_expected'] and receipt['original_root_unchanged']
        save('copied-controls-replay.json', {
            'invocation': result, 'receipt': receipt,
            'fresh_output_only_on_disposable_copy': True,
            'original_author_control_receipt_preserved': True})
    after = inventory(AUTHOR)
    assert before == after
    save('author-unchanged.json', {
        'scope': 'INTEGRITY_ONLY', 'entire_author_root_unchanged': True,
        'before': before, 'after': after, 'copied_temporary_directories_removed': True})
    print(json.dumps({'integrity': 'PASS', 'canonical_sources': 21,
                      'copied_controls': 23, 'finite_identity_receipt_matched': True,
                      'author_unchanged': True, 'mathematical_gate': False}))


if __name__ == '__main__':
    main()
