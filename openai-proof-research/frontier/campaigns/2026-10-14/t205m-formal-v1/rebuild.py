#!/usr/bin/env python3
"""Fresh scoped support compilation and kernel-dependency audit; MIT, Myeongjin Kang."""
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
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True, help='new directory outside the frozen package')
    parser.add_argument('--cache', type=Path, default=CACHE)
    parser.add_argument('--lean', type=Path, default=LEAN)
    args = parser.parse_args()
    out = Path(args.output).resolve()
    require(not out.is_relative_to(HERE) and not HERE.is_relative_to(out),
            'output must be outside the package and cannot contain it')
    out.mkdir(parents=True, exist_ok=False)
    receipt = {'status': 'RUNNING', 'full_theorem_formalized': False,
               'independent_review': False, 'network_used': False,
               'dependency_cache_modified': False, 'runs': [], 'sources': {}}
    try:
        lock = json.loads((HERE / 'lake-manifest.json').read_text())
        libs, pins = [], {}
        for entry in lock['packages']:
            dep = args.cache / entry['name']
            actual = subprocess.check_output(['git', '-C', str(dep), 'rev-parse', 'HEAD'], text=True).strip()
            require(actual == entry['rev'], 'dependency pin mismatch: ' + entry['name'])
            dirty = subprocess.check_output(['git', '-C', str(dep), 'status', '--porcelain', '--untracked-files=no'], text=True)
            require(not dirty.strip(), 'tracked dependency modified: ' + entry['name'])
            pins[entry['name']] = actual
            lib = dep / '.lake/build/lib/lean'
            if lib.is_dir():
                libs.append(str(lib.resolve()))
        require(pins['mathlib'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612', 'wrong mathlib')
        version = subprocess.check_output([str(args.lean), '--version'], text=True).strip()
        require('4.34.1' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version,
                'wrong Lean compiler')
        receipt.update(dependencies=pins, lean_version=version, lean_binary_sha256=sha(args.lean.read_bytes()))
        sources = {'T205M.lean': 'T205M', 'Controls.lean': 'T205MControls'}
        declarations = {}
        for filename, namespace in sources.items():
            code = (HERE / filename).read_text()
            require(not re.search(r'\b(?:sorry|admit|unsafe|native_decide)\b|^\s*axiom\s', code, re.M),
                    'forbidden proof escape: ' + filename)
            names = re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)', code, re.M)
            require(names, 'missing declarations')
            declarations[filename] = [(namespace + '.' + name) for name in names]
            receipt['sources'][filename] = sha(code.encode())
        with tempfile.TemporaryDirectory(prefix='.fresh-build-', dir=out) as directory:
            build = Path(directory)
            env = os.environ.copy()
            env['LEAN_PATH'] = os.pathsep.join([str(build)] + libs)
            for filename in sources:
                (build / filename).write_bytes((HERE / filename).read_bytes())
            audit = ''.join('import ' + Path(f).stem + '\n' for f in sources)
            audit += '\n'.join('#check @' + name + '\n#print axioms ' + name
                               for names in declarations.values() for name in names) + '\n'
            (build / 'Checks.lean').write_text(audit)
            (out / 'Checks.lean').write_text(audit)
            steps = [('support', ['-o', 'T205M.olean', 'T205M.lean']),
                     ('controls', ['-o', 'Controls.olean', 'Controls.lean']),
                     ('types-axioms', ['Checks.lean'])]
            for label, argv in steps:
                result = subprocess.run([str(args.lean), *argv], cwd=build, env=env,
                                        capture_output=True, text=True)
                text = result.stdout + result.stderr
                (out / (label + '.log')).write_text(text)
                receipt['runs'].append({'step': label, 'exit_code': result.returncode,
                                        'output_sha256': sha(text.encode())})
                require(result.returncode == 0 and not re.search(r'\b(?:error|warning):', text),
                        'compile failed or warned: ' + label)
            text = (out / 'types-axioms.log').read_text()
            reports = {}
            for names in declarations.values():
                for name in names:
                    match = re.search("'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", text)
                    if match:
                        axioms = set(re.split(r',\s*', re.sub(r'\.\{[^}]*\}', '', match.group(1)).strip())) - {''}
                    else:
                        require("'" + name + "' does not depend on any axioms" in text, 'missing axiom report: ' + name)
                        axioms = set()
                    require(axioms <= STANDARD, 'unapproved axiom dependency: ' + name)
                    reports[name] = sorted(axioms)
            receipt['kernel_dependencies'] = reports
            receipt['declarations'] = declarations
        receipt['status'] = 'PASS_SCOPED_SOURCE_BUILD_TYPES_AND_STANDARD_AXIOMS'
        print(receipt['status'])
        print('Support declarations:', len(declarations['T205M.lean']))
        print('Control declarations:', len(declarations['Controls.lean']))
    except Exception as error:
        receipt.update(status='FAILED', error=str(error))
        raise
    finally:
        (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')

if __name__ == '__main__':
    main()
