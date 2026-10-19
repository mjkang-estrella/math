#!/usr/bin/env python3
"""Parent integrity-only replay on the original and disposable copies. MIT."""
import hashlib
import json
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
REPO = Path(__file__).resolve().parents[4]
AUTHOR = HERE.parent/'fresh-arithmetic-discovery-r83'
FINAL = '39f782cf7b9ab4a2baef86ec977c9ba34c8bb93677eeaee3a558db17feb68806'
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def save(n, d):
    (HERE/n).write_text(json.dumps(d, indent=2)+'\n')

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
    hashes = {'FINAL.json': FINAL,
        'MANIFEST.json': 'a63a1fcbede83f1056378428b40efa7b5035d7c12ef946d01abc09e05fd0162e',
        'REPORT.md': 'e92901af6b298b49eae99667276d33719b1ec79bd191cca9ae2e7b732f23c4d6',
        'controls/results.json': 'c5d8f7c526407e88f67f2aa56a52af01784b823a20622f547f8326a9d001f887'}
    assert all(sha((AUTHOR/n).read_bytes()) == h for n,h in hashes.items())
    verifier = AUTHOR/'packet/public/verify.py'
    receipt = run([sys.executable, '-I', '-B', str(verifier), '--root', str(AUTHOR), '--finalhash', FINAL])
    save('integrity-replay.json', receipt)
    tb = (REPO/'sources/preprints-tree.json').read_bytes()
    assert sha(tb) == TREE
    tree = json.loads(tb)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    actual = {e['path']: e for e in tree['tree']}
    selection = json.loads((AUTHOR/'packet/private/canonical-selection.json').read_text())
    assert selection['tree_sha256'] == TREE and selection['entry_count'] == 13223
    selected = selection['entries']
    assert len(selected) == 20 and len({e['path'] for e in selected}) == 20
    assert all(actual[e['path']] == e for e in selected)
    save('canonical-replay.json', {'scope': 'INTEGRITY_ONLY', 'tree_sha256': TREE,
        'entries': 13223, 'truncated': False, 'full_selected_records_matched': 20,
        'external_hashes_matched': hashes, 'mathematical_gate': False})
    with tempfile.TemporaryDirectory(prefix='copied-controls-', dir=HERE) as temp:
        copy = Path(temp)/'author-copy'
        shutil.copytree(AUTHOR, copy, symlinks=True)
        result = run([sys.executable, '-I', '-B', str(copy/'packet/public/run_copied_controls.py'),
                      '--root', str(copy), '--finalhash', FINAL])
        controls = json.loads((copy/'controls/results.json').read_text())
        assert len(controls['cases']) == 13 and all(c['passed'] for c in controls['cases'])
        assert controls['all_expected'] and controls['original_unchanged']
        save('copied-controls-replay.json', {'invocation': result, 'receipt': controls})
    after = inventory(AUTHOR)
    assert before == after
    save('author-unchanged.json', {'scope': 'INTEGRITY_ONLY', 'entire_author_root_unchanged': True,
        'before': before, 'after': after, 'copied_temporary_directories_removed': True})
    print(json.dumps({'integrity': 'PASS', 'canonical_sources': 20, 'copied_controls': 13,
                      'author_unchanged': True, 'mathematical_gate': False}))

if __name__ == '__main__':
    main()
