#!/usr/bin/env python3
"""Detached evidence intake; copied integrity cases only, no mathematical gate."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

MANIFEST = '8ef799b43a7072a6924cf98ae543835de974d43e5903bba2436a79264c971b01'
REPORT = '38ca4149f3127a3585ab287e9ac7123ab0c14f84c51aef37c105444ba499f31a'
PUBLIC_REPORT = '5a8c6787dc7fb0c75c9f0887ecf458df5359eba73018c0564c6aa661e39c65d1'
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def snapshot(root):
    result = {}
    for p in [root, *sorted(root.rglob('*'))]:
        s = p.lstat(); value = [s.st_mode, s.st_nlink]
        if stat.S_ISREG(s.st_mode): value += [s.st_size, sha(p)]
        elif stat.S_ISLNK(s.st_mode): value += [os.readlink(p)]
        result[p.relative_to(root).as_posix()] = value
    return result


def run(args):
    r = subprocess.run(args, capture_output=True, text=True,
                       env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    assert r.returncode == 0, r.stdout + r.stderr
    return json.loads(r.stdout)


def main():
    parent = Path(__file__).resolve().parent
    author = parent.parent / 'fresh-structural-discovery-r127'
    repo = author.parents[3]; tree = repo / 'sources/preprints-tree.json'
    assert (author / 'FINAL.sha256').read_text().strip() == MANIFEST
    assert sha(author / 'packet/MANIFEST.json') == MANIFEST
    assert sha(author / 'REPORT.md') == REPORT
    assert (author / 'REPORT.sha256').read_text().strip() == REPORT
    assert sha(author / 'packet/public/report.md') == PUBLIC_REPORT
    assert sha(tree) == TREE
    assert (parent / 'controls-original.py').read_bytes() == (author / 'scratch/controls.py').read_bytes()
    before = snapshot(author); tree_before = snapshot(tree.parent)[tree.name]
    verification = run([sys.executable, '-B', str(author / 'packet/public/verify.py'),
                        '--packet', str(author / 'packet'), '--finalhash', str(author / 'FINAL.sha256'),
                        '--tree', str(tree)])
    with tempfile.TemporaryDirectory(prefix='.replay-', dir=parent) as td:
        tmp = Path(td); copy = tmp / 'frontier/campaigns/2026-10-14/author'
        shutil.copytree(author, copy)
        assert snapshot(copy) == before
        (tmp / 'sources').mkdir(); shutil.copy2(tree, tmp / 'sources/preprints-tree.json')
        wrapper = tmp / 'wrapper.py'
        wrapper.write_text('''import json, os, runpy, stat, subprocess, sys, hashlib
from pathlib import Path
selected = Path(sys.argv[1]); scratch = selected.parent
def snap(root):
 out = {}
 for p in [root, *sorted(root.rglob('*'))]:
  s = p.lstat(); v = [s.st_mode, s.st_nlink]
  if stat.S_ISREG(s.st_mode): v += [s.st_size, hashlib.sha256(p.read_bytes()).hexdigest()]
  elif stat.S_ISLNK(s.st_mode): v += [os.readlink(p)]
  out[p.relative_to(root).as_posix()] = v
 return out
original_run = subprocess.run; calls = []
def guarded(*args, **kwargs):
 before = snap(scratch)
 result = original_run(*args, **kwargs)
 unchanged = before == snap(scratch)
 calls.append(unchanged)
 assert unchanged, 'copied verifier mutated an input'
 return result
subprocess.run = guarded
runpy.run_path(str(selected), run_name='__main__')
Path(sys.argv[2]).write_text(json.dumps(calls))
''')
        original_tree = sha(tmp / 'sources/preprints-tree.json')
        summary = run([sys.executable, '-B', str(wrapper), str(copy / 'scratch/controls.py'), str(tmp / 'calls.json')])
        receipt = json.loads((copy / 'controls.json').read_text())
        calls = json.loads((tmp / 'calls.json').read_text())
        assert summary['cases'] == 17 and summary['all_expected'] and summary['original_unchanged']
        assert len(calls) == 17 and all(calls)
        assert len(receipt['cases']) == 17
        assert all(x['as_expected'] and x['copy_unchanged_by_verifier'] for x in receipt['cases'])
        assert sha(tmp / 'sources/preprints-tree.json') == original_tree
    assert snapshot(author) == before
    assert snapshot(tree.parent)[tree.name] == tree_before
    result = {'status': 'ARTIFACTS_ONLY', 'detached_manifest_sha256': MANIFEST,
              'detached_report_sha256': REPORT, 'verification': verification,
              'controls': receipt['cases'], 'all_copied_inputs_unchanged': True,
              'whole_actual_author_root_unchanged': True, 'external_canonical_tree_unchanged': True,
              'selected_runner_and_verifier_unmodified': True,
              'limits': '17 integrity cases only. Original scratch runner is preserved separately; wrapper adds full per-invocation scratch/input snapshots. Exact packet bytes, modes, single-link regular types and directories are sealed; detached FINAL mode and full outside-root inventory are not sealed. Parent separately preserves all actual bytes/types/modes/link counts. No hostile-code or race certification, mathematical test or gate.'}
    (parent / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'cases_expected': 17, 'originals_unchanged': True, 'verification': verification}))


if __name__ == '__main__': main()
