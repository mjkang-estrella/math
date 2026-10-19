#!/usr/bin/env python3
"""Detached candidate authentication and disposable-copy artifact replay."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

FINAL = '8419adc4398f7b682aa3ee5f5e08397d90e2815d2869fffde4bd6f64ee4de28d'
REPORT = '26aaf530d6ce6d6fc20e8265937fe416945eb968efe451bf42e95b1491a77587'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def full_snapshot(root):
    rows = {}
    for p in [root] + sorted(root.rglob('*')):
        s = p.lstat(); value = [s.st_mode, s.st_nlink]
        if stat.S_ISREG(s.st_mode): value += [s.st_size, sha(p)]
        elif stat.S_ISLNK(s.st_mode): value += [os.readlink(p)]
        rows[p.relative_to(root).as_posix()] = value
    return rows


def run(args):
    p = subprocess.run(args, capture_output=True, text=True)
    assert p.returncode == 0, p.stdout + p.stderr
    return json.loads(p.stdout)


def main():
    parent = Path(__file__).resolve().parent
    author = parent.parent / 'fresh-analytic-discovery-r126'
    tree = parent.parent.parents[2] / 'sources/preprints-tree.json'
    before = full_snapshot(author)
    assert sha(author / 'packet/MANIFEST.json') == FINAL
    assert (author / 'FINAL').read_text() == FINAL + '\n'
    assert sha(author / 'REPORT.md') == REPORT
    assert sha(tree) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    assert (author / 'packet/private/context/preprints-tree.json').read_bytes() == tree.read_bytes()
    options = ['--expected-final', FINAL, '--expected-report', REPORT]
    verification = run([sys.executable, '-B', str(author / 'packet/public/verify.py'), '--root', str(author)] + options)
    with tempfile.TemporaryDirectory(prefix='.replay-', dir=parent) as tmp:
        work = Path(tmp); copy = work / 'author'
        shutil.copytree(author, copy)
        assert full_snapshot(copy) == before
        source = (copy / 'packet/public/controls.py').read_text()
        definition = '''def full_snapshot(root):
 rows={}
 for p in [root]+sorted(root.rglob('*')):
  s=p.lstat();v=[s.st_mode,s.st_nlink]
  if stat.S_ISREG(s.st_mode):v += [s.st_size,hashlib.sha256(p.read_bytes()).hexdigest()]
  elif stat.S_ISLNK(s.st_mode):v += [os.readlink(p)]
  rows[p.relative_to(root).as_posix()]=v
 return rows
'''
        source = source.replace('import subprocess\n', 'import subprocess\nimport stat\n', 1)
        source = source.replace('def run():', definition + '\ndef run():', 1)
        token = '            r=subprocess.run(cmd,capture_output=True,text=True,timeout=30)'
        assert source.count(token) == 1
        source = source.replace(token, '            copied_before=full_snapshot(copy)\n' + token +
                                '\n            unchanged=full_snapshot(copy)==copied_before\n            assert unchanged,name')
        source = source.replace("'matched':r.returncode==expected,", "'matched':r.returncode==expected,'parent_inputs_unchanged':unchanged,")
        helper = work / 'instrumented_controls.py'; helper.write_text(source)
        receipt = run([sys.executable, '-B', str(helper), '--root', str(copy)] + options)
        assert len(receipt['controls']) == 19 and receipt['all_expected'] and receipt['whole_original_root_restored_unchanged']
        assert all(x['matched'] and x['parent_inputs_unchanged'] for x in receipt['controls'])
    assert full_snapshot(author) == before
    result = {'status': 'ARTIFACTS_ONLY', 'detached_manifest_final': FINAL, 'detached_report_sha256': REPORT,
              'verification': verification, 'controls': receipt, 'external_canonical_tree_matches': True,
              'whole_actual_author_root_unchanged': True,
              'parent_instrumentation': 'Outside-copy derivative runner adds full per-copy byte/mode/link-count snapshots; FINAL-bound runner and selected authenticated-original verifier remain unchanged.',
              'limits': 'Manifest seals bytes/sizes and exact names, not modes or hardlinks. Parent preservation separately compares these. Original runner has no per-copy snapshots and tracks original names/bytes only. Ordinary mutants test enclosing seals; no mathematical or hostile-code/race certification.'}
    (parent / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'cases_expected': 19, 'actual_original_unchanged': True, 'verification': verification}))


if __name__ == '__main__': main()
