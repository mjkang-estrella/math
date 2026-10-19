#!/usr/bin/env python3
"""Read-only parent authentication and disposable control replay. MIT. No math gate."""
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
AUTHOR = HERE.parent/'fresh-analytic-discovery-r118'
FINAL = 'eab82a5b0c08d673de6fdbadcc89ab106c592dea5a726136195651b8f8eb3c03'
REPORT = 'c87878236d7d184353eeae5977a8d58e5b1e57103fd0d46ae8f9354b4647a5ea'
MANIFEST = 'c7dbf31aa1d7f0eeee2a1e0d35b2f156849c97ec6370e9be47ce149aefdc767a'
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
    for n, h in [('FINAL.json', FINAL), ('MANIFEST.json', MANIFEST),
                 ('packet/public/report.md', REPORT),
                 ('controls/results.json', 'ca08ad02c51a5528b90b319d904b1fa683d434fb4aff8b5c850815fcfb561feb')]:
        assert sha((AUTHOR/n).read_bytes()) == h, n
    treepath = REPO/'sources/preprints-tree.json'
    tb = treepath.read_bytes()
    assert sha(tb) == TREE
    tree = json.loads(tb)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    canonical = {e['path']: e for e in tree['tree']}
    sources = json.loads((AUTHOR/'packet/public/source-register.json').read_text())
    assert len(sources) == 25 and len({s['path'] for s in sources}) == 25
    for s in sources:
        e = canonical[s['path']]
        assert e['type'] == 'blob' and e['sha'] == s['git_blob'] and e['size'] == s['bytes']
        assert s['url'] == 'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+s['path']
    save('canonical-replay.json', {'scope': 'INTEGRITY_ONLY', 'canonical_records': 25,
        'tree_sha256': TREE, 'entries': 13223, 'truncated': False,
        'path_type_blob_size_and_raw_url_matched': True, 'mathematical_gate': False})
    verifier = AUTHOR/'packet/public/verify.py'
    common = ['--tree', str(treepath), '--finalhash', FINAL, '--reporthash', REPORT]
    receipt = run([sys.executable, '-I', '-B', str(verifier), '--root', str(AUTHOR), *common])
    save('integrity-replay.json', receipt)
    with tempfile.TemporaryDirectory(prefix='copied-controls-', dir=HERE) as temp:
        copy = Path(temp)/'author-copy'
        shutil.copytree(AUTHOR, copy, symlinks=True)
        result = run([sys.executable, '-I', '-B', str(copy/'packet/public/run-copied-controls.py'),
                      '--root', str(copy), *common])
        controls = json.loads((copy/'controls/results.json').read_text())
        assert len(controls['cases']) == 19 and all(c['passed'] for c in controls['cases'])
        assert controls['original_unchanged']
        save('copied-controls-replay.json', {'invocation': result, 'receipt': controls})
    after = inventory(AUTHOR)
    assert before == after
    save('author-unchanged.json', {'scope': 'INTEGRITY_ONLY', 'entire_author_root_unchanged': True,
        'before': before, 'after': after, 'copied_temporary_directories_removed': True})
    print(json.dumps({'integrity': 'PASS', 'canonical_sources': 25, 'copied_controls': 19,
                      'author_unchanged': True, 'mathematical_gate': False}))

if __name__ == '__main__':
    main()
