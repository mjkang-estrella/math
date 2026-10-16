#!/usr/bin/env python3
"""Fresh copied-source compilation using existing read-only pinned caches.
Copyright 2026 Myeongjin Kang. MIT license. No network or dependency builds.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
LEAN = Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
CACHE = HERE.parent / 'formal/.lake/packages'
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', type=Path, default=LEAN)
    parser.add_argument('--cache', type=Path, default=CACHE)
    args = parser.parse_args()
    logs = HERE / 'logs'
    logs.mkdir(exist_ok=True)
    # Remove stale success evidence before any prerequisite checks.
    (HERE / 'validation.json').write_text(json.dumps({'status': 'running; not validated'}) + '\n')
    lock = json.loads((HERE / 'lake-manifest.json').read_text())
    libs, revisions = [], {}
    for package in lock['packages']:
        path = args.cache / package['name']
        actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
        if actual != package['rev']:
            raise ValueError(('Dependency revision mismatch', package['name'], actual))
        revisions[package['name']] = actual
        lib = path / '.lake/build/lib/lean'
        if lib.is_dir():
            libs.append(str(lib.resolve()))
    if revisions['mathlib'] != 'd13f23b723b8a846827a245b89c10fc7d3f11612':
        raise ValueError('Wrong mathlib pin')
    if not (args.cache / 'mathlib/.lake/build/lib/lean').is_dir():
        raise ValueError('Compiled mathlib dependency cache missing')
    version = subprocess.check_output([str(args.lean), '--version'], text=True).strip()
    if '4.34.1' not in version or '5045d0056413266e57c625dcd7c365b10e377c52' not in version:
        raise ValueError('Wrong Lean compiler')
    (logs / 'compiler-version.txt').write_text(version + '\n')
    source = (HERE / 'StaircaseSupport.lean').read_text()
    names = re.findall(r'^(?:@\[simp\] )?(?:def|theorem) (\w+)', source, re.M)
    theorems = re.findall(r'^(?:@\[simp\] )?theorem (\w+)', source, re.M)
    checks = (HERE / 'Checks.lean').read_text()
    for name in names:
        if f'#check @StaircaseSupport.{name}\n' not in checks or f'#print axioms StaircaseSupport.{name}\n' not in checks:
            raise ValueError('Public declaration missing from type/axiom audit: ' + name)
    source_files = ['StaircaseSupport.lean', 'Checks.lean', 'Controls.lean']
    for name in source_files:
        if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', (HERE / name).read_text()):
            raise ValueError('Forbidden source token: ' + name)
    runs = []
    result = {'status': 'running', 'lean_version': version,
              'lean_executable': str(args.lean.resolve()), 'cache_directory': str(args.cache.resolve()),
              'dependency_revisions': revisions,
              'source_sha256': sha(source.encode()), 'theorems': theorems,
              'public_declarations': names, 'runs': runs,
              'full_staircase_theorem_formalized': False,
              'independent_semantic_review': False, 'acceptance_awarded': False,
              'network_used': False, 'dependencies_rebuilt': False,
              'preexisting_support_olean_used': False,
              'compilation_writes': 'disposable copy inside the assigned directory only'}
    with tempfile.TemporaryDirectory(prefix='.build-', dir=HERE) as directory:
        temp = Path(directory)
        env = os.environ.copy()
        env['LEAN_PATH'] = os.pathsep.join([str(temp)] + libs)
        for name in source_files:
            (temp / name).write_bytes((HERE / name).read_bytes())
        for name, command, expected_count in [
            ('source', ['-o', 'StaircaseSupport.olean', 'StaircaseSupport.lean'], 0),
            ('types-and-axioms', ['Checks.lean'], len(names)),
            ('controls', ['-o', 'Controls.olean', 'Controls.lean'], 6),
        ]:
            run = subprocess.run([str(args.lean), *command], cwd=temp, env=env,
                                 capture_output=True, text=True, timeout=300)
            output = run.stdout + run.stderr
            (logs / (name + '.log')).write_text(output)
            axiom_rows = re.findall(r'depends on axioms: \[([^\]]*)\]', output)
            axiom_sets = [set(re.sub(r'\.\{[^}]*\}', '', row).split(', ')) - {''} for row in axiom_rows]
            ok = (run.returncode == 0 and 'warning:' not in output and 'sorryAx' not in output
                  and len(axiom_rows) == expected_count
                  and all(row <= STANDARD_AXIOMS for row in axiom_sets))
            runs.append({'name': name, 'args': command, 'exit_code': run.returncode,
                         'log_sha256': sha(output.encode()), 'passed': ok,
                         'axiom_reports': len(axiom_rows),
                         'axioms': sorted(set().union(*axiom_sets)) if axiom_sets else []})
            if not ok:
                result['status'] = 'failed: ' + name
                (HERE / 'validation.json').write_text(json.dumps(result, indent=2) + '\n')
                print(output, end='')
                raise SystemExit(1)
        result['fresh_support_olean_sha256'] = sha((temp / 'StaircaseSupport.olean').read_bytes())
    result['status'] = 'PASS: fresh scoped support compilation and kernel-checked counterexamples'
    (HERE / 'validation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
