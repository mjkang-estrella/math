#!/usr/bin/env python3
"""Parent proof-review authentication and disposable-copy controls; artifacts only."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

FINAL = '2d654e1996d02ccc202a7f4b9e05e7f1326532c67e9506be240b9b579454495c'
REPORT = '5c2120eae516567f54a1f745d2cb950614ec2173baae6155f74b540939e38d24'
CONTROLS = '18a85fdaa9b421a185bcab2656b6b3b3d6ebac56060816ae769b10a011689517'


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def snapshot(root):
    out = {}
    for p in [root] + sorted(root.rglob('*')):
        s = p.lstat(); v = [s.st_mode, s.st_nlink]
        if stat.S_ISREG(s.st_mode): v += [s.st_size, sha(p)]
        elif stat.S_ISLNK(s.st_mode): v += [os.readlink(p)]
        out[p.relative_to(root).as_posix()] = v
    return out


def run(args):
    p = subprocess.run(args, capture_output=True, text=True)
    assert p.returncode == 0, p.stdout + p.stderr
    return json.loads(p.stdout)


def main():
    parent = Path(__file__).resolve().parent; campaign = parent.parent
    project = campaign.parents[2]
    review = campaign / 't096n126-proof-r1'; author = campaign / 'fresh-analytic-discovery-r126'
    before = {'review': snapshot(review), 'author': snapshot(author)}
    assert sha(review / 'packet/MANIFEST.json') == FINAL
    assert (review / 'FINAL').read_text() == FINAL + '\n'
    assert sha(review / 'REPORT.md') == REPORT and sha(review / 'work/controls-result.json') == CONTROLS
    options = ['--project-root', str(project), '--expected-final', FINAL, '--expected-report', REPORT]
    verification = run([sys.executable, '-B', str(review / 'packet/public/verify.py'), '--root', str(review)] + options)
    with tempfile.TemporaryDirectory(prefix='.proof-r1-', dir=parent) as tmp:
        work = Path(tmp); copy = work / 'review'; shutil.copytree(review, copy)
        assert snapshot(copy) == before['review']
        source = (copy / 'packet/public/controls.py').read_text()
        definition = '''def full_snapshot(root):
 out={}
 for p in [root]+sorted(root.rglob('*')):
  s=p.lstat();v=[s.st_mode,s.st_nlink]
  if stat.S_ISREG(s.st_mode):v += [s.st_size,hashlib.sha256(p.read_bytes()).hexdigest()]
  elif stat.S_ISLNK(s.st_mode):v += [os.readlink(p)]
  out[p.relative_to(root).as_posix()]=v
 return out
'''
        source = source.replace('import subprocess\n', 'import subprocess\nimport stat\n', 1)
        source = source.replace('def main():', definition + '\ndef main():', 1)
        token = '            outcome = check(target, seal, report)'
        assert source.count(token) == 1
        source = source.replace(token, '            parent_before = full_snapshot(target)\n' + token +
                                '\n            parent_unchanged = parent_before == full_snapshot(target)\n            assert parent_unchanged, name')
        source = source.replace("'copy_bytes_unchanged_by_verifier': True", "'copy_bytes_unchanged_by_verifier': True, 'parent_full_inputs_unchanged': parent_unchanged")
        helper = work / 'instrumented_controls.py'; helper.write_text(source)
        summary = run([sys.executable, '-B', str(helper), '--root', str(copy)] + options)
        receipt = json.loads((copy / 'work/controls-result.json').read_text())
        copied = [x for x in receipt['cases'] if x['name'] not in {'original_before', 'original_after'}]
        assert summary['controls'] == 'PASS' and summary['disposable_cases'] == 15 and len(copied) == 15
        assert all(x['parent_full_inputs_unchanged'] for x in copied)
        assert all((x['returncode'] == 0) == (x['expected'] == 'PASS') for x in receipt['cases'])
    assert before == {'review': snapshot(review), 'author': snapshot(author)}
    result = {'status': 'REVIEW_ARTIFACTS_ONLY', 'detached_manifest_final': FINAL,
              'detached_report_sha256': REPORT, 'detached_controls_sha256': CONTROLS,
              'verification': verification, 'controls': receipt,
              'whole_actual_review_root_unchanged': True, 'whole_actual_author_root_unchanged': True,
              'parent_instrumentation': 'Outside-copy derivative runner adds full per-copy byte/mode/link snapshots; authenticated manifest-bound runner and original selected verifier remain unchanged.',
              'limits': '15 copied cases include expected acceptance of unbound modes/hardlinks; two additional original verifications. Manifest binds bytes/sizes/names/directories and regular types, not modes/nlinks. Parent independently preserves those attributes for whole actual roots. No mathematical or hostile-code/race certification.'}
    (parent / 'proof-r1-replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'copied_cases_expected': 15, 'author_and_review_originals_unchanged': True, 'verification': verification}))


if __name__ == '__main__': main()
