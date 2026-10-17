#!/usr/bin/env python3
"""Fresh source build; all writes stay in this assigned directory.
Copyright 2026 Myeongjin Kang. MIT. Reuses pinned dependency objects read-only.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from checked_run import run_checked

HERE = Path(__file__).resolve().parent
DEFAULT_LEAN = Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
DEFAULT_CACHE = HERE.parent / 'formal/.lake/packages'
LEAN_COMMIT = '5045d0056413266e57c625dcd7c365b10e377c52'
MATHLIB_COMMIT = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
SOURCES = ['TSLocal.lean', 'Controls.lean', 'Checks.lean', 'ControlChecks.lean']


def sha(data):
    return hashlib.sha256(data).hexdigest()


def declarations(path):
    return re.findall(r'^(?:@\[simp\] )?(?:noncomputable )?(?:def|theorem|instance) (\w+)', path.read_text(), re.M)


def audit_output(output, namespace, names):
    reports = {}
    for name in names:
        full = f'{namespace}.{name}'
        match = re.search(r"'" + re.escape(full) + r"' depends on axioms: \[([^\]]*)\]", output)
        if match:
            row = re.sub(r'\.\{[^}]*\}', '', match.group(1))
            axioms = set(re.split(r',\s*', row.strip())) - {''}
        elif f"'{full}' does not depend on any axioms" in output:
            axioms = set()
        else:
            raise ValueError('Missing axiom report: ' + full)
        if not axioms <= STANDARD_AXIOMS:
            raise ValueError(('Unapproved kernel dependency', full, axioms))
        if full not in output:
            raise ValueError('Missing exact declaration type: ' + full)
        reports[full] = sorted(axioms)
    return reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', type=Path, default=DEFAULT_LEAN)
    parser.add_argument('--cache', type=Path, default=DEFAULT_CACHE)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    out = args.output or Path('.replays') / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    out = (HERE / out).resolve()
    if not out.is_relative_to(HERE) or out == HERE:
        raise ValueError('Build output must be a new subdirectory of the assigned package')
    out.mkdir(parents=True, exist_ok=False)
    result = {'status': 'RUNNING', 'full_TS132_theorem_formalized': False,
              'independent_audit': False, 'network_used': False,
              'dependency_cache_modified': False, 'previous_support_objects_used': False,
              'source_sha256': {s: sha((HERE/s).read_bytes()) for s in SOURCES},
              'runs': []}
    try:
        lock = json.loads((HERE/'lake-manifest.json').read_text())
        libs, pins = [], {}
        for package in lock['packages']:
            path = args.cache / package['name']
            actual = subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'], text=True).strip()
            if actual != package['rev']:
                raise ValueError(('Dependency pin mismatch', package['name'], actual))
            dirty = subprocess.check_output(['git','-C',str(path),'status','--porcelain','--untracked-files=no'], text=True)
            if dirty.strip():
                raise ValueError(('Tracked dependency changes', package['name'], dirty))
            pins[package['name']] = actual
            lib = path/'.lake/build/lib/lean'
            if lib.is_dir():
                libs.append(str(lib.resolve()))
        if pins['mathlib'] != MATHLIB_COMMIT:
            raise ValueError('Wrong mathlib revision')
        version_run = subprocess.run([str(args.lean),'--version'], capture_output=True, text=True, check=True)
        (out/'compiler-version.stdout').write_text(version_run.stdout)
        (out/'compiler-version.stderr').write_text(version_run.stderr)
        if '4.34.1' not in version_run.stdout or LEAN_COMMIT not in version_run.stdout:
            raise ValueError('Wrong Lean compiler')
        result.update(lean_version=version_run.stdout.strip(), dependency_revisions=pins,
                      lean_binary_sha256=sha(args.lean.read_bytes()),
                      lean_executable=str(args.lean.resolve()), cache_directory=str(args.cache.resolve()))
        names = declarations(HERE/'TSLocal.lean')
        cnames = declarations(HERE/'Controls.lean')
        for source, audit, namespace, entries in [
                ('TSLocal.lean','Checks.lean','TSLocal',names),
                ('Controls.lean','ControlChecks.lean','TSControls',cnames)]:
            text = (HERE/audit).read_text()
            for name in entries:
                if f'#check @{namespace}.{name}\n' not in text or f'#print axioms {namespace}.{name}\n' not in text:
                    raise ValueError('Unaudited public declaration: ' + name)
            code = (HERE/source).read_text()
            if re.search(r'\b(?:sorry|admit|unsafe|native_decide)\b|^\s*axiom\s', code, re.M):
                raise ValueError('Forbidden source command: ' + source)
        result['support_declarations'] = names
        result['support_theorems'] = re.findall(r'^(?:@\[simp\] )?theorem (\w+)', (HERE/'TSLocal.lean').read_text(), re.M)
        result['control_declarations'] = cnames
        result['control_theorems'] = re.findall(r'^theorem (\w+)', (HERE/'Controls.lean').read_text(), re.M)
        with tempfile.TemporaryDirectory(prefix='.compile-', dir=HERE) as directory:
            build = Path(directory)
            for source in SOURCES:
                (build/source).write_bytes((HERE/source).read_bytes())
            env = os.environ.copy()
            env['LEAN_PATH'] = os.pathsep.join([str(build)] + libs)
            env['PYTHONDONTWRITEBYTECODE'] = '1'
            steps = [('support',['-o','TSLocal.olean','TSLocal.lean']),
                     ('examples',['-o','Controls.olean','Controls.lean']),
                     ('types-axioms',['Checks.lean']),
                     ('example-types-axioms',['ControlChecks.lean'])]
            for label, command in steps:
                run = run_checked([str(args.lean),*command], build, env, out/label)
                if 'warning:' in run.stdout + run.stderr:
                    raise ValueError('Compiler warning in ' + label)
                result['runs'].append({'name':label,'exit_code':run.returncode,
                                      'command':['lean',*command],
                                      'stdout_sha256':sha(run.stdout.encode()),
                                      'stderr_sha256':sha(run.stderr.encode())})
            result['axiom_reports'] = audit_output((out/'types-axioms.stdout').read_text(), 'TSLocal',names)
            result['control_axiom_reports'] = audit_output((out/'example-types-axioms.stdout').read_text(), 'TSControls',cnames)
            # Run the exact arithmetic and the failure-marker controls from source.
            run = run_checked([sys.executable,'-B',str(HERE/'semantic_checks.py')], build, env, out/'semantic-checks')
            result['runs'].append({'name':'semantic-checks','exit_code':run.returncode,
                                  'stdout_sha256':sha(run.stdout.encode()),'stderr_sha256':sha(run.stderr.encode())})
        result['status'] = 'PASS scoped source build, exact types, standard axioms and semantic controls'
        print(result['status'])
        print(f"Support: {len(result['support_theorems'])} theorems; {len(names)} public declarations; controls: {len(result['control_theorems'])} theorems, {len(cnames)} declarations")
    except Exception as exc:
        result['status'] = 'FAILED'
        result['error'] = str(exc)
        raise
    finally:
        (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__ == '__main__':
    main()
