#!/usr/bin/env python3
"""Parent byte authentication and disposable integrity controls. MIT. No math gate."""
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
AUTHOR = HERE.parent/'fresh-arithmetic-discovery-r84'
FINAL = '4ee83b085753ca934ebf58767e568dfa89569ad638272d6189edce8e80cda521'
REPORT = '7c276274b75a9c4fb81e304313947a4ae7875ddf11807468e41b27ef86c8baf1'
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
        'MANIFEST.json': 'fb44aef48d663618ac19360923ba594ddd76bfbdfebc4e3a2f57042031b57b3e',
        'controls/results.json': '867741c39c54333c4e72c899612f40a0b962d71d570bdd15cf73575ce10c4485'}
    assert all(sha((AUTHOR/n).read_bytes()) == h for n,h in hashes.items())
    treepath = REPO/'sources/preprints-tree.json'
    tb = treepath.read_bytes()
    assert sha(tb) == TREE
    tree = json.loads(tb)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    canonical = {e['path']: e for e in tree['tree']}
    sources = json.loads((AUTHOR/'packet/public/source-register.json').read_text())
    assert len(sources) == 32 and len({e['path'] for e in sources}) == 32
    for s in sources:
        e = canonical[s['path']]
        assert e['type'] == 'blob' and e['sha'] == s['git_blob'] and e['size'] == s['bytes']
        assert s['raw_url'] == 'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+s['path']
    save('canonical-replay.json', {'scope': 'INTEGRITY_ONLY', 'tree_sha256': TREE,
        'entries': 13223, 'truncated': False, 'source_records': 32,
        'path_type_blob_size_pinned_raw_url_matched': True,
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
        assert len(controls['controls']) == 16 and all(c['as_expected'] for c in controls['controls'])
        assert controls['original_unchanged']
        save('copied-controls-replay.json', {'invocation': result, 'receipt': controls})
    after = inventory(AUTHOR)
    assert before == after
    save('author-unchanged.json', {'scope': 'INTEGRITY_ONLY', 'entire_author_root_unchanged': True,
        'before': before, 'after': after, 'copied_temporary_directories_removed': True})
    print(json.dumps({'integrity': 'PASS', 'canonical_sources': 32, 'copied_controls': 16,
                      'author_unchanged': True, 'mathematical_gate': False}))

if __name__ == '__main__':
    main()
