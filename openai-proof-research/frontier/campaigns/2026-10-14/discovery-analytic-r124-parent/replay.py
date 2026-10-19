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
AUTHOR = HERE.parent / 'fresh-analytic-discovery-r124'
FINAL = 'e85e59893f6855bfbbac3129c59bf9332ffdc3f26ba7be1dfdf9594cb85ed576'
REPORT = '8f54439bec8a5586aa6b3e5b4bcc0e464b9d6dcf4fb4a18ce865c6aed6908245'
MANIFEST = 'f4f905daa2a79bcf204edec76916714b2b4762129cf186ab210281311800d4ae'
PUBLIC = '3ea3e55cad10c161506aaafa39d0cea08c0d4f66ce31037f47abab4c2b4c4d89'
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
              'MANIFEST.json': MANIFEST, 'packet/public/report.md': PUBLIC}
    assert all(sha((AUTHOR / n).read_bytes()) == h for n, h in hashes.items())
    treepath = REPO / 'sources/preprints-tree.json'
    tb = treepath.read_bytes()
    assert sha(tb) == TREE
    assert (AUTHOR / 'packet/private/context/preprints-tree.json').read_bytes() == tb
    tree = json.loads(tb)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    canonical = {e['path']: e for e in tree['tree']}
    assert len(canonical) == 13223
    retained = json.loads((AUTHOR / 'packet/public/canonical.json').read_text())
    removed = json.loads((AUTHOR / 'packet/public/removed-acquisitions.json').read_text())
    assert len(retained) == 15 and len(removed) == 69
    assert len({s['path'] for s in retained + removed}) == 84
    for s in retained + removed:
        e = canonical[s['path']]
        assert e == s['tree_entry'] and e['type'] == s['type'] == 'blob'
        assert e['sha'] == s['blob'] and e['size'] == s['size']
        assert s['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + s['path']
    save('canonical-replay.json', {
        'scope': 'INTEGRITY_ONLY', 'tree_sha256': TREE, 'entries': 13223,
        'truncated': False, 'source_records': 84, 'retained': 15, 'removed': 69,
        'all_full_canonical_records_path_type_blob_size_pinned_raw_url_matched': True,
        'removed_bodies_not_rehashed': True, 'external_hashes_matched': hashes,
        'mathematical_gate': False})
    save('integrity-replay.json', run([
        sys.executable, '-I', '-B', str(AUTHOR / 'packet/public/verify.py'),
        '--root', str(AUTHOR), '--finalhash', FINAL, '--reporthash', REPORT,
        '--tree', str(treepath)]))
    with tempfile.TemporaryDirectory(prefix='copied-controls-', dir=HERE) as temp:
        copy = Path(temp) / 'author-copy'
        shutil.copytree(AUTHOR, copy, symlinks=True)
        assert sha((copy / 'FINAL.json').read_bytes()) == FINAL
        assert sha((copy / 'REPORT.md').read_bytes()) == REPORT
        out = copy / 'parent-controls.json'
        assert not out.exists() and not (copy / 'scratch/copied-controls-r1').exists()
        result = run([
            sys.executable, '-I', '-B', str(copy / 'packet/public/controls.py'),
            '--root', str(copy), '--output', str(out), '--tree', str(treepath)])
        receipt = json.loads(out.read_text())
        cases = receipt['cases']
        assert len(cases) == 19 and len({c['case'] for c in cases}) == 19
        assert all(c['expected_outcome'] and c['copy_unchanged'] for c in cases)
        assert sum(c['exit'] == 0 for c in cases) == 1
        assert next(c for c in cases if c['case'] == 'baseline')['exit'] == 0
        assert receipt['final_sha256'] == FINAL and receipt['outside_report_sha256'] == REPORT
        assert receipt['all_expected'] and receipt['whole_original_root_unchanged_before_receipt']
        save('copied-controls-replay.json', {
            'invocation': result, 'receipt': receipt,
            'runner_derives_hashes_from_previously_parent_authenticated_copy': True,
            'fresh_output_only_on_disposable_copy': True,
            'original_author_controls_preserved': True})
    after = inventory(AUTHOR)
    assert before == after
    save('author-unchanged.json', {
        'scope': 'INTEGRITY_ONLY', 'entire_author_root_unchanged': True,
        'before': before, 'after': after, 'copied_temporary_directories_removed': True})
    print(json.dumps({'integrity': 'PASS', 'canonical_records': 84, 'retained_sources': 15,
                      'copied_controls': 19, 'author_unchanged': True,
                      'mathematical_gate': False}))


if __name__ == '__main__':
    main()
