#!/usr/bin/env python3
"""Parent integrity and bounded-diagnostic replay. No mathematical gate. MIT."""
import hashlib
import json
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

REPO = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
AUTHOR = HERE.parent / 'fresh-structural-discovery-r119'
FINAL = 'be019575fb7dac51e0edee4e832a1a42dfe90ffcf36e78fdf1f8c10109a6a006'
# Full immutable tree hash (keep distinct from its Git tree object ID).
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def save(name, obj):
    (HERE / name).write_text(json.dumps(obj, indent=2) + '\n')

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
    hashes = {n: sha((AUTHOR/n).read_bytes()) for n in ['FINAL.json', 'MANIFEST.json', 'REPORT.md']}
    assert hashes == {'FINAL.json': FINAL,
        'MANIFEST.json': 'd4c772407d64828e36c31fc63bec7e70111cc2fb2b1855f420d7df5294afd5d1',
        'REPORT.md': 'fadf2104af2d82484199f8c3e3d97ba691950ce008e5f7e0c43432e5b67d633d'}
    verifier = AUTHOR/'packet/public/verify.py'
    check = run([sys.executable, '-I', '-B', str(verifier), '--root', str(AUTHOR), '--finalhash', FINAL])
    save('integrity-replay.json', check)
    tb = (REPO/'sources/preprints-tree.json').read_bytes()
    assert sha(tb) == TREE
    tree = json.loads(tb)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    actual = {e['path']: e for e in tree['tree']}
    selected = json.loads((AUTHOR/'packet/private/canonical-selection.json').read_text())
    assert selected['tree_sha256'] == TREE
    assert len(selected['selected']) == 25
    assert len({e['path'] for e in selected['selected']}) == 25
    assert all(actual[e['path']] == e for e in selected['selected'])
    public = json.loads((AUTHOR/'packet/public/source-register.json').read_text())
    private = json.loads((AUTHOR/'packet/private/source-provenance.json').read_text())
    assert len(public) == len(private) == 25
    for p, q in zip(public, private):
        assert p['path'] == q['path'] and p['url'] == q['raw_url']
        assert p['sha256'] == q['sha256'] and p['git_blob'] == q['git_blob']
        assert p['bytes'] == len((AUTHOR/'packet'/p['local']).read_bytes())
    final = json.loads((AUTHOR/'FINAL.json').read_text())
    assert sha((AUTHOR/'packet/public/report.md').read_bytes()) == final['public_report_sha256']
    save('canonical-replay.json', {'scope': 'INTEGRITY_ONLY', 'tree_sha256': TREE,
        'entries': 13223, 'truncated': False, 'full_selected_entries_matched': 25,
        'public_source_metadata_matched': True, 'external_hashes': hashes,
        'public_report_sha256': final['public_report_sha256'], 'mathematical_gate': False})
    with tempfile.TemporaryDirectory(prefix='copied-controls-', dir=HERE) as temp:
        copied = Path(temp)/'author-copy'
        shutil.copytree(AUTHOR, copied, symlinks=True)
        result = run([sys.executable, '-I', '-B', str(copied/'packet/public/run_copied_controls.py'),
                      '--root', str(copied), '--finalhash', FINAL])
        controls = json.loads((copied/'controls/results.json').read_text())
        assert len(controls['cases']) == 13 and controls['all_expected'] and controls['original_unchanged']
        assert sum(c['expected'] == 'accept' for c in controls['cases']) == 1
        save('copied-controls-replay.json', {'invocation': result, 'receipt': controls})
    diagnostic = run([sys.executable, '-I', '-B', str(AUTHOR/'packet/public/finite_checks.py')])
    sealed = json.loads((AUTHOR/'packet/public/finite-results.json').read_text())
    assert json.loads(diagnostic['stdout']) == sealed
    save('finite-replay.json', {'invocation': diagnostic, 'matches_sealed_json': True,
                              'mathematical_gate': False})
    after = inventory(AUTHOR)
    assert before == after
    save('author-unchanged.json', {'scope': 'INTEGRITY_ONLY', 'entire_author_root_unchanged': True,
        'before': before, 'after': after, 'copied_temporary_directories_removed': True})
    print(json.dumps({'integrity': 'PASS', 'controls': 13, 'canonical_records': 25,
                      'finite_matches': True, 'author_unchanged': True, 'mathematical_gate': False}))

if __name__ == '__main__':
    main()
