#!/usr/bin/env python3
"""Parent prefreeze artifact intake and copied exact checks; no math gate."""
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
ROOT = HERE.parent / 'fresh-structural-discovery-r138'
OLDS = [HERE.parent / ('fresh-structural-discovery-r' + str(n)) for n in (136, 137)]
ANCHORS = {
    'final': '8d738c83a73e1192519a1d5e2636cfe1d74a28763d19c78ad964b710ace011a8',
    'manifest': '7770e6af2211c8bac5a9c90c94dce89d46b69d612fec7dedefa58011b7c8c8e6',
    'report': '506d78213baaf75e52b2b59a2aaf63c2c1cb9a81f6e59b68822bfc336af7d31a',
}


def record(p):
    s = p.lstat()
    r = {'mode': stat.S_IMODE(s.st_mode), 'type': stat.S_IFMT(s.st_mode), 'links': s.st_nlink}
    if p.is_symlink():
        r['target'] = str(p.readlink())
    elif p.is_file():
        r.update(bytes=s.st_size, sha256=hashlib.sha256(p.read_bytes()).hexdigest())
    return r


def snap(root):
    return {str(p.relative_to(root)): record(p) for p in [root, *root.rglob('*')]}


def run(args):
    r = subprocess.run(args, text=True, capture_output=True)
    assert r.returncode == 0, (args, r.returncode, r.stderr)
    return {'exit': r.returncode, 'stdout': r.stdout, 'stderr': r.stderr}


def command(root, script):
    cmd = [sys.executable, '-B', str(root / 'packet/public' / script), '--root', str(root), '--project', str(PROJECT)]
    for k, v in ANCHORS.items():
        cmd += ['--' + k + '-sha256', v]
    return cmd


def main():
    roots = [ROOT, *OLDS]
    before = {str(r): snap(r) for r in roots}
    regs = json.loads((ROOT / 'packet/private/input-bindings.json').read_text())['files']
    stable = [r for r in regs if r.get('role') != 'observation']
    assert len(regs) == 43 and len(stable) == 40
    originals = {r['path']: record(PROJECT / r['path']) for r in stable}
    for r in stable:
        assert originals[r['path']]['sha256'] == r['sha256'] and originals[r['path']]['bytes'] == r['bytes']
    result = {'kind': 'PARENT_PREFREEZE_ARTIFACT_INTAKE_NO_MATHEMATICAL_GATE', 'anchors': ANCHORS,
              'original_verification': run(command(ROOT, 'verify.py'))}
    with tempfile.TemporaryDirectory(prefix='copy-', dir=HERE) as td:
        copy = Path(td) / ROOT.name
        copy.mkdir()
        shutil.copytree(ROOT / 'packet', copy / 'packet')
        for name in ('FINAL.json', 'REPORT.md'):
            shutil.copy2(ROOT / name, copy / name)
        result['copied_controls'] = run(command(copy, 'run_copied_controls.py'))
        cases = json.loads((copy / 'work/copied-controls-receipt.json').read_text())
        assert len(cases) == 6 and all(r['expected_behavior'] for r in cases)
        assert [r['case'] for r in cases] == ['baseline', 'payload', 'extra', 'report', 'symlink', 'forged-reseal']
        result['control_cases'] = cases
        result['finite_exact_diagnostic'] = run([sys.executable, '-B', str(copy / 'packet/public/check_math.py')])
        math = json.loads(result['finite_exact_diagnostic']['stdout'])
        assert math == json.loads((ROOT / 'packet/private/math-receipt.json').read_text())
        assert len(math['nontight_cases']) == 6
        assert [r['exact_common_count_vectors'] for r in math['nontight_cases'][:3]] == [264, 1404, 4512]
        result['copied_after_controls_verification'] = run(command(copy, 'verify.py'))
    assert all(record(PROJECT / rel) == r for rel, r in originals.items())
    unchanged = {str(r.relative_to(PROJECT)): snap(r) == before[str(r)] for r in roots}
    assert all(unchanged.values())
    result.update(all_expected=True, verification_summary=json.loads(result['original_verification']['stdout']),
                  stable_named_originals_unchanged=40, archival_observations=3, copied_cases=6,
                  math_receipt_identical=True, whole_actual_roots_unchanged=unchanged,
                  accepted=False, count_change=0, mathematical_gate=False)
    result['limits'] = (
        'Exact62-payload packet and detached anchors;40 stable named originals/copies and3 archival copies. '
        'Verifier additionally checks old136/137 sealed packets,137s74 bindings/40source blobs/six primary versions. '
        'Complete current actual136/137/138 roots including work and40 stable originals unchanged during replay; '
        'not historical whole-parent preservation or fresh reading of every source/primary body. Six unmodified '
        'supplied copied controls check expected exit behavior,not independent per-fixture syscall/failure-reason audits. '
        'Finite exact six-parameter/allcut/rank/resistance/repair/enumeration/exchange diagnostics match author receipt; '
        'no independent correctness,contribution,priority,impossibility,full theorem or acceptance gate.')
    (HERE / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('all_expected', 'verification_summary', 'stable_named_originals_unchanged',
        'archival_observations', 'copied_cases', 'math_receipt_identical', 'whole_actual_roots_unchanged')}))


if __name__ == '__main__':
    main()
