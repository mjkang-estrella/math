#!/usr/bin/env python3
"""Parent authentication and disposable integrity/audit controls. MIT. No math gate."""
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
AUTHOR = HERE.parent/'fresh-analytic-discovery-r121'
FINAL = '100785893cf37f714c0d4c5bdfa20190185927e2f3a269a178cb3b7733d07db5'
REPORT = '85b352c0a168ea110a60ac1faa45a98621ce6eec1440256565270f7a2e75869f'
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
    hashes = {'FINAL.json': FINAL, 'packet/public/report.md': REPORT,
        'MANIFEST.json': '28b8951ef8befa07feea82f41d000e1ca01bbc20aafbf2aa31bf85769b8f429d'}
    assert all(sha((AUTHOR/n).read_bytes()) == h for n,h in hashes.items())
    treepath = REPO/'sources/preprints-tree.json'
    tb = treepath.read_bytes()
    assert sha(tb) == TREE
    tree = json.loads(tb)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    canonical = {e['path']: e for e in tree['tree']}
    sources = json.loads((AUTHOR/'packet/public/source-register.json').read_text())
    assert len(sources) == 18 and len({e['path'] for e in sources}) == 18
    for s in sources:
        e = canonical[s['path']]
        assert e['type'] == 'blob' and e['sha'] == s['blob'] and e['size'] == s['bytes']
        assert s['url'] == 'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+s['path']
    save('canonical-replay.json', {'scope': 'INTEGRITY_ONLY', 'tree_sha256': TREE,
        'entries': 13223, 'truncated': False, 'source_records': 18,
        'path_type_blob_size_pinned_raw_url_matched': True,
        'external_hashes_matched': hashes, 'mathematical_gate': False})
    common = ['--tree', str(treepath), '--finalhash', FINAL, '--reporthash', REPORT]
    verifier = AUTHOR/'packet/public/verify.py'
    save('integrity-replay.json', run([sys.executable, '-I', '-B', str(verifier), str(AUTHOR), *common]))
    with tempfile.TemporaryDirectory(prefix='copied-controls-', dir=HERE) as temp:
        copy = Path(temp)/'author-copy'
        shutil.copytree(AUTHOR, copy, symlinks=True)
        # The runner refuses existing output; remove only the DISPOSABLE COPY's prior receipts.
        shutil.rmtree(copy/'work/controls')
        result = run([sys.executable, '-I', '-B', str(copy/'packet/public/controls.py'), str(copy), *common])
        controls = json.loads((copy/'work/controls/receipt.json').read_text())
        assert len(controls['controls']) == 19 and all(c['as_expected'] for c in controls['controls'])
        assert sum(c['expected'] == 'success' for c in controls['controls']) == 3
        assert controls['all_as_expected'] and controls['original_root_unchanged_excluding_only_control_output_subtree']
        save('copied-controls-replay.json', {'invocation': result, 'receipt': controls,
            'removed_only_disposable_copy_prior_control_output': True})
    after = inventory(AUTHOR)
    assert before == after
    save('author-unchanged.json', {'scope': 'INTEGRITY_ONLY', 'entire_author_root_unchanged': True,
        'before': before, 'after': after, 'copied_temporary_directories_removed': True})
    print(json.dumps({'integrity': 'PASS', 'canonical_sources': 18, 'copied_controls': 19,
                      'author_unchanged': True, 'mathematical_gate': False}))

if __name__ == '__main__':
    main()
