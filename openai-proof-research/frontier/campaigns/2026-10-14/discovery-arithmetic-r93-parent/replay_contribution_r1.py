#!/usr/bin/env python3
"""Detached contribution-review authentication and copied integrity replay."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

FINAL = 'b8b23ff7485426491a6da80cbc97b046f4ae3939aeb4b29acb54ef6cf17c42cc'
REVIEW = '197e60df9418355ec0cb907f898121f86d45beca26056aea76e9cc1aa2665bb6'
MANIFEST = '8c466cbbdd4eedaba3813829288e14cc39f005c8cbe27230c95edd50eb5e90e6'
CONTROLS = '65ea7a8ca3f27fe81726504db78486ba842e9edd63eb53fb28613694058ff575'


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def snapshot(root):
    result = {}
    for p in [root, *sorted(root.rglob('*'))]:
        s = p.lstat(); value = [s.st_mode, s.st_nlink]
        if stat.S_ISREG(s.st_mode): value += [s.st_size, sha(p)]
        elif stat.S_ISLNK(s.st_mode): value += [os.readlink(p)]
        result[p.relative_to(root).as_posix()] = value
    return result


def inputs(repo, names):
    return {name: snapshot(repo / name)['.'] for name in names}


def run(args):
    r = subprocess.run(args, capture_output=True, text=True,
                       env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    assert r.returncode == 0, r.stdout + r.stderr
    return json.loads(r.stdout)


def main():
    parent = Path(__file__).resolve().parent
    review = parent.parent / 't195d93-contribution-r1'
    author = parent.parent / 'fresh-arithmetic-discovery-r93'
    repo = author.parents[3]
    assert sha(review / 'FINAL.json') == FINAL and sha(review / 'REVIEW.md') == REVIEW
    assert sha(review / 'MANIFEST.json') == MANIFEST and sha(review / 'CONTROLS.json') == CONTROLS
    reading = json.loads((review / 'public/reading.json').read_text())
    names = sorted(set(reading['detached_author_anchors']) |
                   {x['path'] for x in reading['bodies']} |
                   {reading['preprints_tree']['path'], reading['pinned_source']['path']})
    assert len(names) == 20
    before_review = snapshot(review); before_author = snapshot(author)
    before_inputs = inputs(repo, names)
    direct = run([sys.executable, '-I', '-B', str(review / 'public/verify.py'),
                  '--root', str(review), '--repo', str(repo), '--final-sha256', FINAL])
    with tempfile.TemporaryDirectory(prefix='.contribution-r1-', dir=parent) as td:
        tmp = Path(td); copied_repo = tmp / 'repo'
        copied_review = copied_repo / review.relative_to(repo)
        copied_author = copied_repo / author.relative_to(repo)
        shutil.copytree(review, copied_review); shutil.copytree(author, copied_author)
        for name in names:
            target = copied_repo / name
            if not target.exists():
                target.parent.mkdir(parents=True, exist_ok=True); shutil.copy2(repo / name, target)
        assert snapshot(copied_review) == before_review and snapshot(copied_author) == before_author
        assert inputs(copied_repo, names) == before_inputs
        wrapper = tmp / 'wrapper.py'
        wrapper.write_text('''import hashlib, json, os, runpy, stat, subprocess, sys
from pathlib import Path
selected = Path(sys.argv[1]); calls_file = Path(sys.argv[2])
names = json.loads(Path(sys.argv[3]).read_text()); anchor = sys.argv[4]
def snap(root):
 out = {}
 for p in [root, *sorted(root.rglob('*'))]:
  s = p.lstat(); v = [s.st_mode, s.st_nlink]
  if stat.S_ISREG(s.st_mode): v += [s.st_size, hashlib.sha256(p.read_bytes()).hexdigest()]
  elif stat.S_ISLNK(s.st_mode): v += [os.readlink(p)]
  out[p.relative_to(root).as_posix()] = v
 return out
original_run = subprocess.run; calls = []
def guarded(args, **kwargs):
 target = Path(args[args.index('--root')+1]); repo = Path(args[args.index('--repo')+1])
 before = [snap(target), {n: snap(repo/n)['.'] for n in names}]
 result = original_run(args, **kwargs)
 unchanged = before == [snap(target), {n: snap(repo/n)['.'] for n in names}]
 calls.append(unchanged); assert unchanged, 'copied verifier changed selected input'
 return result
subprocess.run = guarded
sys.argv = [str(selected), '--final-sha256', anchor]
try: runpy.run_path(str(selected), run_name='__main__')
except SystemExit as e:
 assert e.code in (None, 0), e
calls_file.write_text(json.dumps(calls))
''')
        (tmp / 'inputs.json').write_text(json.dumps(names))
        summary = run([sys.executable, '-B', str(wrapper), str(copied_review / 'public/run_controls.py'),
                       str(tmp / 'calls.json'), str(tmp / 'inputs.json'), FINAL])
        receipt = json.loads((copied_review / 'CONTROLS.json').read_text())
        calls = json.loads((tmp / 'calls.json').read_text())
        assert summary['all_as_expected'] and summary['originals_unchanged']
        assert len(calls) == 13 and all(calls)
        assert len(receipt['cases']) == 13 and all(x['as_expected'] for x in receipt['cases'])
        assert sum(x['observed_ok'] for x in receipt['cases']) == 2
        assert snapshot(copied_author) == before_author and inputs(copied_repo, names) == before_inputs
        changed = snapshot(copied_review); changed.pop('CONTROLS.json')
        expected = dict(before_review); expected.pop('CONTROLS.json')
        assert changed == expected
    assert snapshot(review) == before_review and snapshot(author) == before_author
    assert inputs(repo, names) == before_inputs
    result = {'status': 'ARTIFACTS_ONLY', 'detached_review_final_sha256': FINAL,
              'detached_review_sha256': REVIEW, 'locally_observed_controls_sha256': CONTROLS,
              'verification': direct, 'controls': receipt,
              'copied_cases_expected': 13, 'per_invocation_full_copied_target_and20_inputs_unchanged': True,
              'whole_actual_author_root_unchanged': True, 'whole_actual_review_root_unchanged': True,
              'external20_inputs_unchanged': True, 'selected_runner_and_verifier_unmodified': True,
              'limits': '13 artifact cases:2 accepted baselines and11 rejected mutants. Wrapper adds full copied-target and20 external input byte/type/mode/link snapshots per invocation, leaving selected sealed runner/verifier unchanged. Own original snapshot covers29 file entries but not directories/full author root; parent adds whole-root preservation. Own seal binds7 payloads/3 nonroot directories, excludes root mode,two seal files,CONTROLS and scratch. External checks are20 hashes plus source Git blob/tree match, not full author verification. No explicit audit-denial probes, mathematical test/gate or hostile-runtime/race guarantee.'}
    (parent / 'contribution-r1-replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'copied_cases_expected': 13, 'originals_unchanged': True, 'verification': direct}))


if __name__ == '__main__': main()
