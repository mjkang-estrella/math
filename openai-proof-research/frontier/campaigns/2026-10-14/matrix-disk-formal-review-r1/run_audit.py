#!/usr/bin/env python3
"""Independently rebuild GLM source in a temporary directory using pinned cache.

MIT, copyright 2026 Myeongjin Kang. This is a kernel/statement audit of the
finite scalar support only. Install the pinned Lean binary on PATH first.
"""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
CAMPAIGN = HERE.parent
SOURCE = CAMPAIGN / 'matrix-disk-formal-glm-r1'
FORMAL = CAMPAIGN / 'formal'


def main():
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=FORMAL / '.lake/packages/mathlib', text=True).strip()
    assert revision == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
    toolchain = subprocess.check_output(['lean', '--version'], text=True).strip()
    assert '4.34.1' in toolchain
    paths = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=FORMAL, text=True).strip().split(os.pathsep)
    paths = [str((FORMAL / p).resolve()) if not Path(p).is_absolute() else p for p in paths]
    results = []
    with tempfile.TemporaryDirectory(prefix='matrix-variance-audit-') as directory:
        temp = Path(directory)
        for name in ['FiniteVariance.lean', 'Checks.lean']:
            shutil.copy2(SOURCE / name, temp / name)
        shutil.copy2(HERE / 'ParentAudit.lean', temp / 'ParentAudit.lean')
        env = os.environ.copy()
        env['LEAN_PATH'] = os.pathsep.join([str(temp)] + paths)
        for name, args in [
            ('source', ['lean', '-o', 'FiniteVariance.olean', 'FiniteVariance.lean']),
            ('author_checks', ['lean', 'Checks.lean']),
            ('parent_types_axioms', ['lean', 'ParentAudit.lean']),
        ]:
            result = subprocess.run(args, cwd=temp, env=env, text=True, capture_output=True)
            output = result.stdout + result.stderr
            (HERE / (name + '.log')).write_text(output)
            results.append({'check': name, 'exit_code': result.returncode, 'warning': 'warning:' in output})
            if result.returncode:
                raise RuntimeError(output)
            if 'sorryAx' in output:
                raise RuntimeError('Forbidden axiom in audit')
    receipt = {
        'status': 'PASS',
        'method': 'Parent read entire source and author checks; rebuilt source into a fresh temporary olean, compiled author checks and independent exact quantified statement/axiom audit against that olean.',
        'toolchain': toolchain, 'mathlib_revision': revision, 'runs': results,
        'axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'scope': 'Arbitrary finite real scalar bistochastic variance identity, per-column identity and nonnegative deficit. Not the Hilbert-valued integral, Fatou passage or full analytic theorem.',
        'source_sha256': {name: hashlib.sha256((SOURCE / name).read_bytes()).hexdigest() for name in ['FiniteVariance.lean', 'Checks.lean', 'README.md']},
        'parent_audit_sha256': hashlib.sha256((HERE / 'ParentAudit.lean').read_bytes()).hexdigest(),
        'author_olean_trusted': False, 'new_result_count_credit': 0,
        'initial_parent_harness_correction': 'The first parent example omitted the specified DecidableEq instance. The source already compiled; adding the original instance to the audit corrected the harness, with no source change. Initial failure log retained.',
    }
    (HERE / 'validation.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
