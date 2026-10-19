#!/usr/bin/env python3
"""Detached proof-review authentication and disposable-copy integrity replay."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

ANCHORS = {
    'FINAL.json': '96a6cee966bc2358b5125cbdf357b1415f975aabb3f1004b727fd34ee5358fcb',
    'REPORT.md': '0937a98410d2f157bc181d3a9f677d04991f756707cf3c541b7f783c41f399a6',
    'packet/MANIFEST.json': '46221ef0399a2143cfefb501db5a6bc18c7a94fb0e818f7631cd0db9ac9baa5f',
    'copied-controls/receipt.json': '41825732fd29348ec5de24cdd9faaf1a5572043264bbed825565a25e25dd083e',
    'author-preservation.json': '69ae0ba186290262db00f4b46b14c0d3e7ba0b35655b721f909d72c33f128dbd',
    'final-verification.json': '854947e835fc3d08806eb6a0455c2698f33b42576ebb87ed2e19ffcb4fd85696',
}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def full_snapshot(root):
    result = {}
    for p in [root] + sorted(root.rglob('*')):
        s = p.lstat()
        value = [s.st_mode, s.st_nlink]
        if stat.S_ISREG(s.st_mode):
            value += [s.st_size, sha(p)]
        elif stat.S_ISLNK(s.st_mode):
            value += [os.readlink(p)]
        result[p.relative_to(root).as_posix()] = value
    return result


def run(args):
    p = subprocess.run(args, capture_output=True, text=True)
    assert p.returncode == 0, p.stdout + p.stderr
    return json.loads(p.stdout)


def main():
    parent = Path(__file__).resolve().parent
    review = parent.parent / 't238b125-proof-r1'
    author = parent.parent / 'fresh-structural-discovery-r125'
    before = {'review': full_snapshot(review), 'author': full_snapshot(author)}
    for name, value in ANCHORS.items():
        assert sha(review / name) == value, name
    author_anchors = json.loads((review / 'packet/private/author-anchors.json').read_text())
    for name, value in author_anchors.items():
        assert sha(author / name) == value, name
    options = ['--finalhash', ANCHORS['FINAL.json'], '--reporthash', ANCHORS['REPORT.md']]
    verification = run([sys.executable, '-B', str(review / 'packet/public/verify.py'), '--root', str(review)] + options)
    with tempfile.TemporaryDirectory(prefix='.proof-r1-', dir=parent) as tmp:
        work = Path(tmp)
        copy = work / 'review'
        shutil.copytree(review, copy)
        assert full_snapshot(copy) == before['review']
        source = (copy / 'packet/public/controls.py').read_text()
        helper_definition = '''def full_snapshot(root):
 result={}
 for p in [root]+sorted(root.rglob('*')):
  s=p.lstat();v=[s.st_mode,s.st_nlink]
  if stat.S_ISREG(s.st_mode):v += [s.st_size,hashlib.sha256(p.read_bytes()).hexdigest()]
  elif stat.S_ISLNK(s.st_mode):v += [os.readlink(p)]
  result[p.relative_to(root).as_posix()]=v
 return result
'''
        token = '        observed = run(case, fh, rh)'
        assert source.count(token) == 1
        source = source.replace('def main():', helper_definition + '\ndef main():', 1)
        source = source.replace(token, '        copied_before = full_snapshot(case)\n' + token +
                                '\n        copied_unchanged = copied_before == full_snapshot(case)\n' +
                                '        assert copied_unchanged, kind\n' +
                                "        observed['parent_copied_inputs_unchanged'] = copied_unchanged")
        helper = work / 'instrumented_controls.py'
        helper.write_text(source)
        summary = run([sys.executable, '-B', str(helper), '--root', str(copy), '--out', 'parent-replay'] + options)
        receipt = json.loads((copy / 'parent-replay/receipt.json').read_text())
        assert summary['all_expected'] and len(receipt['cases']) == 14
        assert receipt['original_review_files_and_modes_unchanged']
        assert all(x['passed'] and x['observed']['parent_copied_inputs_unchanged'] for x in receipt['cases'])
    assert before == {'review': full_snapshot(review), 'author': full_snapshot(author)}
    result = {'status': 'REVIEW_ARTIFACTS_ONLY', 'detached_review_anchors': ANCHORS,
              'all_six_actual_author_anchors_match': True, 'verification': verification,
              'controls': receipt, 'whole_actual_review_root_unchanged': True,
              'whole_actual_author_root_unchanged': True,
              'parent_instrumentation': 'Outside-copy derivative runner adds per-case full byte/mode/link-count snapshots. Selected FINAL-bound runner and verifier are unmodified.',
              'limits': '14 artifact cases only; three use explicit artificial new test anchors for deeper source/transport/verdict checks. No mathematical tests, new correctness proof, hostile-code sandbox or race guarantee.'}
    (parent / 'proof-r1-replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'cases_expected': 14, 'author_and_review_unchanged': True, 'verification': verification}))


if __name__ == '__main__':
    main()
