#!/usr/bin/env python3
"""Parent artifact intake and copied diagnostics; no mathematical gate."""
import hashlib
import json
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[3]
ROOT = HERE.parent / 'fresh-structural-discovery-r137'
OLD = HERE.parent / 'fresh-structural-discovery-r136'
ANCHORS = {
    'final': '9537d5941bfa2408e23195a2bbfb1d2eebbfd1cefedc2b5e9f6eb8b5b6be1962',
    'manifest': '5e0d09cfca28d5e402274ce72ed9115c0ab2eab432124c5143cff3d2c6e103fb',
    'report': '0c3ef87b9687d093a75d0ec0a08ce2df3dad45ccc307a7ab5a48f00fa52cfaf4',
}


def record(path):
    s = path.lstat()
    r = {'mode': stat.S_IMODE(s.st_mode), 'type': stat.S_IFMT(s.st_mode)}
    if stat.S_ISLNK(s.st_mode):
        r['target'] = str(path.readlink())
    elif stat.S_ISREG(s.st_mode):
        r.update(bytes=s.st_size, sha256=hashlib.sha256(path.read_bytes()).hexdigest(), nlink=s.st_nlink)
    return r


def snapshot(root):
    return {str(p.relative_to(root)): record(p) for p in [root, *root.rglob('*')]}


def run(args):
    r = subprocess.run(args, text=True, capture_output=True)
    assert r.returncode == 0, (args, r.returncode, r.stderr)
    return {'exit': r.returncode, 'stdout': r.stdout, 'stderr': r.stderr}


def command(root, script):
    args = [sys.executable, '-B', str(root / 'packet/public' / script),
            '--root', str(root), '--project', str(PROJECT)]
    for key, value in ANCHORS.items():
        args += ['--' + key + '-sha256', value]
    return args


def main():
    roots_before = {str(r): snapshot(r) for r in (ROOT, OLD)}
    bindings = json.loads((ROOT / 'packet/private/input-bindings.json').read_text())['files']
    assert len(bindings) == len({e['path'] for e in bindings}) == 74
    originals = {e['path']: record(PROJECT / e['path']) for e in bindings}
    for e in bindings:
        assert originals[e['path']]['sha256'] == e['sha256']
        assert originals[e['path']]['bytes'] == e['bytes']
    result = {'kind': 'PARENT_PREFREEZE_ARTIFACT_INTAKE_NO_MATHEMATICAL_GATE', 'anchors': ANCHORS}
    result['actual_original_verification'] = run(command(ROOT, 'verify.py'))
    with tempfile.TemporaryDirectory(prefix='copy-', dir=HERE) as td:
        copy = Path(td) / ROOT.name
        copy.mkdir()
        shutil.copytree(ROOT / 'packet', copy / 'packet')
        for name in ('FINAL.json', 'REPORT.md'):
            shutil.copy2(ROOT / name, copy / name)
        result['copied_controls'] = run(command(copy, 'run_copied_controls.py'))
        controls = json.loads((copy / 'work/control-receipt.json').read_text())
        assert controls['all_expected'] and len(controls['cases']) == 8
        assert [e['case'] for e in controls['cases']] == [
            'baseline', 'payload', 'extra', 'final', 'manifest', 'report', 'symlink', 'forged-reseal']
        result['copied_control_cases'] = controls['cases']
        result['finite_diagnostic'] = run([sys.executable, '-B', str(copy / 'packet/public/check_math.py')])
        math = json.loads(result['finite_diagnostic']['stdout'])
        assert math == json.loads((ROOT / 'packet/private/math-check-receipt.json').read_text())
        assert len(math['fan_cases']) == 20 and math['K4_pairings_checked'] == 15
        assert math['paired_covariance'] and math['parallel_K4_countercheck']
        result['copied_after_controls'] = run(command(copy, 'verify.py'))
    assert all(record(PROJECT / rel) == r for rel, r in originals.items())
    result['whole_actual_roots_unchanged'] = {
        str(r.relative_to(PROJECT)): snapshot(r) == roots_before[str(r)] for r in (ROOT, OLD)}
    assert all(result['whole_actual_roots_unchanged'].values())
    result.update(all_expected=True, stable_originals_unchanged=74, copied_controls_total=8,
                  math_receipt_identical=True,
                  verification_summary=json.loads(result['actual_original_verification']['stdout']))
    result['limits'] = (
        'Full current r137 and r136 roots, including unsealed work, and 74 named original files were '
        'hash/layout snapshotted before/after this replay. This is not historical preservation evidence '
        'or semantic reading of every private body. The eight unmodified supplied fixture controls '
        'check expected return-code behavior, not independent per-fixture syscall/read-only or '
        'failure-reason audits. Whole actual roots and named originals stayed unchanged. Exact finite '
        'diagnostics match the sealed author receipt; no full theorem, correctness, contribution, '
        'exhaustion, priority or acceptance gate is assigned.')
    (HERE / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('all_expected', 'verification_summary',
        'stable_originals_unchanged', 'whole_actual_roots_unchanged', 'copied_controls_total',
        'math_receipt_identical')}, sort_keys=True))


if __name__ == '__main__':
    main()
