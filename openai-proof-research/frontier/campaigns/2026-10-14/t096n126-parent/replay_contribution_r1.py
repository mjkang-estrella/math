#!/usr/bin/env python3
"""Parent authentication and instrumented artifact replay of contribution R1."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

FINAL = 'b69e072445b6923c4b541049293183d7bf5917ef4ffdf7de442e81eec70de3d5'
REPORT = '87a81863a6ab657c8226130b117f29bcc3fa620003eb45116f50fb1b456f19d3'


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
    r = subprocess.run(args, capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr
    return json.loads(r.stdout)


def main():
    parent = Path(__file__).resolve().parent; campaign = parent.parent; project = campaign.parents[2]
    review = campaign / 't096n126-contribution-r1'; author = campaign / 'fresh-analytic-discovery-r126'
    before = {'review': snapshot(review), 'author': snapshot(author)}
    assert sha(review / 'packet/MANIFEST.json') == FINAL and sha(review / 'REPORT.md') == REPORT
    assert (review / 'FINAL').read_text().strip() == FINAL
    original_receipt_sha = sha(review / 'controls-result.json')
    options = ['--project', str(project), '--expected-final', FINAL, '--expected-report', REPORT]
    verification = run([sys.executable, '-B', str(review / 'packet/public/verify.py'), '--root', str(review)] + options)
    with tempfile.TemporaryDirectory(prefix='.contribution-r1-', dir=parent) as tmp:
        work = Path(tmp); copy = work / 'review'; shutil.copytree(review, copy)
        assert snapshot(copy) == before['review']
        source = (copy / 'packet/public/controls.py').read_text()
        definition = '''PARENT_CHECKS=[]
def full_snapshot(root):
 out={}
 for p in [root]+sorted(root.rglob('*')):
  s=p.lstat();v=[s.st_mode,s.st_nlink]
  if stat.S_ISREG(s.st_mode):v += [s.st_size,hashlib.sha256(p.read_bytes()).hexdigest()]
  elif stat.S_ISLNK(s.st_mode):v += [os.readlink(p)]
  out[p.relative_to(root).as_posix()]=v
 return out
def input_snapshot(root,project):
 out={}
 rows=json.loads((Path(root)/'packet/public/inputs.json').read_text())['files']
 for rel in rows:
  p=Path(project)/rel
  if not p.exists():out[rel]=None;continue
  s=p.lstat();v=[s.st_mode,s.st_nlink,s.st_size]
  if stat.S_ISREG(s.st_mode):v.append(hashlib.sha256(p.read_bytes()).hexdigest())
  elif stat.S_ISLNK(s.st_mode):v.append(os.readlink(p))
  out[rel]=v
 return out
'''
        source = source.replace('import sys\n', 'import sys\nimport stat\nfrom pathlib import Path\n', 1)
        source = source.replace('def run_verify(', definition + '\ndef run_verify(', 1)
        token = '    r = subprocess.run(cmd, capture_output=True, text=True)'
        assert source.count(token) == 1
        source = source.replace(token,
            '    parent_before=(full_snapshot(Path(root)),input_snapshot(root,project))\n' + token +
            '\n    parent_after=(full_snapshot(Path(root)),input_snapshot(root,project))\n' +
            '    assert parent_before==parent_after, "verifier mutated inputs"\n' +
            '    PARENT_CHECKS.append({"root_and_recorded_inputs_unchanged":True})')
        source = source.replace('"controls": results,', '"controls": results, "parent_full_input_checks": PARENT_CHECKS,')
        helper = work / 'instrumented_controls.py'; helper.write_text(source)
        receipt = run([sys.executable, '-B', str(helper), '--root', str(copy)] + options)
        assert receipt['status'] == 'PASS' and len(receipt['controls']) == 14 and receipt['originals_unchanged']
        assert all(x['ok'] for x in receipt['controls']) and len(receipt['parent_full_input_checks']) == 14
    assert before == {'review': snapshot(review), 'author': snapshot(author)}
    result = {'status': 'REVIEW_ARTIFACTS_ONLY', 'detached_manifest_final': FINAL,
              'detached_report_sha256': REPORT, 'original_controls_sha256_observed_locally': original_receipt_sha,
              'verification': verification, 'controls': receipt,
              'whole_actual_author_root_unchanged': True, 'whole_actual_review_root_unchanged': True,
              'parent_instrumentation': 'Outside-copy derivative runner adds full byte/mode/link snapshots of each verifier target and its22 listed input originals/mirrors. Manifest-bound selected code and originals unchanged.',
              'limits': 'Own seal binds file bytes/sizes/names; not empty directories, modes, hardlinks or entry types. Own verifier has no audit sandbox and does not independently reject symlinks; run as inspected code. Own runner tracks original file bytes only, parent separately preserves whole actual roots and copied inputs. No mathematical tests or priority/exhaustion inference.'}
    (parent / 'contribution-r1-replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'cases_expected': 14, 'all_copied_inputs_unchanged': True, 'author_and_review_originals_unchanged': True, 'verification': verification}))


if __name__ == '__main__': main()
