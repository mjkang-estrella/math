#!/usr/bin/env python3
"""Parent byte authentication and disposable integrity replay. MIT. No math gate."""
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
AUTHOR = HERE.parent/'fresh-arithmetic-discovery-r86'
FINAL = 'c0dba69cd8088af73d167ef3363fa0afa3219055ff40f72f1c820d16ad96354d'
REPORT = 'c016f0e2b3d8be71dcc46ccb888aa8eea0611d8ee68d41faf4bbdd7ccd1fec52'
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
        'MANIFEST.json': '08eef47c5e9a039b815a292b22f2b44f7d575548d409837c3a2ec0ab5a4291eb'}
    assert all(sha((AUTHOR/n).read_bytes()) == h for n,h in hashes.items())
    treepath = REPO/'sources/preprints-tree.json'
    tb = treepath.read_bytes()
    assert sha(tb) == TREE
    tree = json.loads(tb)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    canonical = {e['path']: e for e in tree['tree']}
    sources = json.loads((AUTHOR/'packet/private/upstream/provenance.json').read_text())
    assert len(sources) == 27 and sum(s['retained'] for s in sources) == 20
    assert len({e['path'] for e in sources}) == 27
    for s in sources:
        e = canonical[s['path']]
        assert e['type'] == 'blob' and e['sha'] == s['git_blob'] and e['size'] == s['bytes']
        assert s['url'] == 'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+s['path']
    save('canonical-replay.json', {'scope': 'INTEGRITY_ONLY', 'tree_sha256': TREE,
        'entries': 13223, 'truncated': False, 'source_metadata_records': 27, 'retained': 20,
        'path_type_blob_size_pinned_raw_url_matched': True,
        'external_hashes_matched': hashes, 'mathematical_gate': False})
    common = ['--tree', str(treepath), '--finalhash', FINAL, '--reporthash', REPORT]
    save('integrity-replay.json', run([sys.executable, '-I', '-B', str(AUTHOR/'verify.py'), '--root', str(AUTHOR), *common]))
    with tempfile.TemporaryDirectory(prefix='copied-controls-', dir=HERE) as temp:
        copy = Path(temp)/'author-copy'
        shutil.copytree(AUTHOR, copy, symlinks=True)
        result = run([sys.executable, '-I', '-B', str(copy/'run_controls.py'), '--root', str(copy), *common])
        controls = json.loads(result['stdout'])
        assert len(controls['controls']) == 17 and all(c['matched_expectation'] for c in controls['controls'])
        assert controls['all_expected'] and controls['original_root_unchanged']
        save('copied-controls-replay.json', {'invocation': result, 'receipt': controls})
    after = inventory(AUTHOR)
    assert before == after
    save('author-unchanged.json', {'scope': 'INTEGRITY_ONLY', 'entire_author_root_unchanged': True,
        'before': before, 'after': after, 'copied_temporary_directories_removed': True})
    print(json.dumps({'integrity': 'PASS', 'canonical_sources': 20, 'copied_controls': 17,
                      'author_unchanged': True, 'mathematical_gate': False}))

if __name__ == '__main__':
    main()
