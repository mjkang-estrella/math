#!/usr/bin/env python3
"""Parent integrity replay. Disposable controls only; no mathematical gate. MIT."""
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
AUTHOR = HERE.parent/'fresh-analytic-discovery-r119'
FINAL = 'dfc463bb867984362bf6fb563a7c9b187fa37224e0a990de946a14a5f18c4241'
REPORT = 'c44b9cee7c44b0d5f8726c50dc316217bcf42fbabbf5bec79968c1b9f2c72184'
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
        'MANIFEST.json': '6c4ff74d45a7737e08e19823d819755ec16fc9598a0b35b9b404f2662c937471',
        'packet/public/report.md': '14476507dea136d79ac23c212182d5719f80d381762b536497a4f6b45d1e90a6',
        'controls/integrity-controls.json': '893e58aa852228bcfda66f4216dfceb92eb973d50ffadfdd7b505a9209655b9d',
        'controls/final-replay.json': '949c42751798c044f1a2b3d9a8d91bdaa1e6df41d2e38836d25f254594c5c344'}
    assert all(sha((AUTHOR/n).read_bytes()) == h for n,h in hashes.items())
    treepath = REPO/'sources/preprints-tree.json'
    tb = treepath.read_bytes()
    assert sha(tb) == TREE
    tree = json.loads(tb)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    canonical = {e['path']: e for e in tree['tree']}
    selection = json.loads((AUTHOR/'packet/public/canonical-selection.json').read_text())
    selected = selection['selected_entries']
    assert selection['tree_sha256'] == TREE
    assert len(selected) == 20 and len({e['path'] for e in selected}) == 20
    assert all(canonical[e['path']] == e for e in selected)
    save('canonical-replay.json', {'scope': 'INTEGRITY_ONLY', 'tree_sha256': TREE,
        'entries': 13223, 'truncated': False, 'full_selected_records_matched': 20,
        'external_hashes_matched': hashes, 'mathematical_gate': False})
    common = ['--tree', str(treepath), '--finalhash', FINAL, '--reporthash', REPORT]
    verifier = AUTHOR/'packet/public/verify.py'
    save('integrity-replay.json', run([sys.executable, '-I', '-B', str(verifier), '--root', str(AUTHOR), *common]))
    with tempfile.TemporaryDirectory(prefix='copied-controls-', dir=HERE) as temp:
        copy = Path(temp)/'author-copy'
        shutil.copytree(AUTHOR, copy, symlinks=True)
        result = run([sys.executable, '-I', '-B', str(copy/'packet/public/integrity_controls.py'),
                      '--root', str(copy), *common])
        controls = json.loads((copy/'controls/integrity-controls.json').read_text())
        assert len(controls['cases']) == 19 and all(c['reason_matched'] for c in controls['cases'])
        assert controls['all_expected'] and controls['original_unchanged'] and controls['temporary_copies_removed']
        save('copied-controls-replay.json', {'invocation': result, 'receipt': controls})
    after = inventory(AUTHOR)
    assert before == after
    save('author-unchanged.json', {'scope': 'INTEGRITY_ONLY', 'entire_author_root_unchanged': True,
        'before': before, 'after': after, 'copied_temporary_directories_removed': True})
    print(json.dumps({'integrity': 'PASS', 'canonical_sources': 20, 'copied_controls': 19,
                      'author_unchanged': True, 'mathematical_gate': False}))

if __name__ == '__main__':
    main()
