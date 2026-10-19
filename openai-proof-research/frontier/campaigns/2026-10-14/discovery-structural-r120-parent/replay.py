#!/usr/bin/env python3
"""Parent authentication and disposable integrity controls only. MIT. No math gate."""
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
AUTHOR = HERE.parent/'fresh-structural-discovery-r120'
FINAL = '287bc2f18199edcccd4450a3774ee4db1f96821036b15d32895d14ffcc3945ad'
REPORT = 'edb3e696457c5ae8d5dd0013bebff183b455027c36e55a7b887ea7a50aca1c2c'
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
    hashes = {'FINAL.json': FINAL, 'REPORT.md': REPORT,
        'MANIFEST.json': '00e1bdab82737983ab58217699253af0cc40203083ce7c4b4f07e6a74ec6b6f7',
        'packet/public/report.md': '7fe4604b140b56f59e6738d3dbcabef011e5bd8ba5187de8f533ebe0e242962c',
        'controls/results.json': '9ab8e3136f99467d8b013bc40a1c6a0513345bfa54bd12e5e28b2b32459f6030'}
    assert all(sha((AUTHOR/n).read_bytes()) == h for n,h in hashes.items())
    treepath = REPO/'sources/preprints-tree.json'
    tb = treepath.read_bytes()
    assert sha(tb) == TREE
    tree = json.loads(tb)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    canonical = {e['path']: e for e in tree['tree']}
    selection = json.loads((AUTHOR/'packet/private/canonical-selection.json').read_text())
    selected = selection['selected']
    assert selection['tree_sha256'] == TREE
    assert len(selected) == 26 and len({e['path'] for e in selected}) == 26
    assert all(canonical[e['path']] == e for e in selected)
    save('canonical-replay.json', {'scope': 'INTEGRITY_ONLY', 'tree_sha256': TREE,
        'entries': 13223, 'truncated': False, 'full_selected_records_matched': 26,
        'external_hashes_matched': hashes, 'mathematical_gate': False})
    common = ['--tree', str(treepath), '--finalhash', FINAL, '--reporthash', REPORT]
    verifier = AUTHOR/'packet/public/verify.py'
    save('integrity-replay.json', run([sys.executable, '-I', '-B', str(verifier), '--root', str(AUTHOR), *common]))
    with tempfile.TemporaryDirectory(prefix='copied-controls-', dir=HERE) as temp:
        copy = Path(temp)/'author-copy'
        shutil.copytree(AUTHOR, copy, symlinks=True)
        result = run([sys.executable, '-I', '-B', str(copy/'packet/public/run_copied_controls.py'),
                      '--root', str(copy), *common])
        controls = json.loads((copy/'controls/results.json').read_text())
        assert len(controls['cases']) == 18 and all(c['passed'] for c in controls['cases'])
        assert controls['all_expected'] and controls['original_unchanged']
        save('copied-controls-replay.json', {'invocation': result, 'receipt': controls})
    after = inventory(AUTHOR)
    assert before == after
    save('author-unchanged.json', {'scope': 'INTEGRITY_ONLY', 'entire_author_root_unchanged': True,
        'before': before, 'after': after, 'copied_temporary_directories_removed': True})
    print(json.dumps({'integrity': 'PASS', 'canonical_sources': 26, 'copied_controls': 18,
                      'author_unchanged': True, 'mathematical_gate': False}))

if __name__ == '__main__':
    main()
