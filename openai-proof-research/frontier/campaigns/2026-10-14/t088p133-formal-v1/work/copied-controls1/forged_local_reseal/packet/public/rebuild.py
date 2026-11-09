#!/usr/bin/env python3
"""Fresh scoped support compilation. MIT, copyright 2026 Myeongjin Kang.
Adapted from t212m-formal-v1/rebuild.py (same author/license); see PROVENANCE.md.
Uses trusted precompiled dependencies read-only, never invokes git/Lake/network.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LEAN = Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
CACHE = ROOT.parent / 'formal/.lake/packages'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def head_revision(dep):
    """Read git metadata without running git or modifying an index/cache."""
    gitdir = dep / '.git'
    if gitdir.is_file():
        gitdir = (dep / gitdir.read_text().strip().removeprefix('gitdir: ')).resolve()
    head = (gitdir / 'HEAD').read_text().strip()
    if not head.startswith('ref: '):
        return head
    ref = head[5:]
    if (gitdir / ref).is_file():
        return (gitdir / ref).read_text().strip()
    for line in (gitdir / 'packed-refs').read_text().splitlines():
        if line.endswith(' ' + ref):
            return line.split()[0]
    raise ValueError('unresolved dependency HEAD: ' + str(dep))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, required=True, help='new directory under package-root/work/')
    ap.add_argument('--cache', type=Path, default=CACHE)
    ap.add_argument('--lean', type=Path, default=LEAN)
    args = ap.parse_args()
    out = args.output.resolve()
    require(out.is_relative_to(ROOT / 'work'), 'output must be under package-root/work')
    out.mkdir(parents=True, exist_ok=False)
    receipt = {'status': 'RUNNING', 'full_theorem_formalized': False, 'independent_review': False,
               'dependency_policy': 'Trust existing precompiled cache; read HEAD pins, no git status or clean-source rebuild.',
               'runs': [], 'sources': {}}
    try:
        lock = json.loads((HERE / 'lake-manifest.json').read_text())
        libs, pins = [], {}
        for entry in lock['packages']:
            dep = args.cache.resolve() / entry['name']
            actual = head_revision(dep)
            require(actual == entry['rev'], 'dependency pin mismatch: ' + entry['name'])
            pins[entry['name']] = actual
            lib = dep / '.lake/build/lib/lean'
            if lib.is_dir():
                libs.append(str(lib))
        require(pins['mathlib'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612', 'wrong mathlib')
        mlock = args.cache / 'mathlib/lake-manifest.json'
        for e in json.loads(mlock.read_text())['packages']:
            require(pins[e['name']] == e['rev'], 'transitive lock mismatch: '+e['name'])
        version = subprocess.check_output([str(args.lean), '--version'], text=True).strip()
        require('4.34.1' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version, 'wrong Lean')
        receipt.update(dependencies=pins, lean_version=version, lean_binary_sha256=sha(args.lean.read_bytes()),
                       dependency_lock_sha256=sha(mlock.read_bytes()))
        sources = {'T088P133.lean': 'T088P133', 'Controls.lean': 'T088P133Controls'}
        declarations = {}
        for filename, namespace in sources.items():
            code = (HERE / filename).read_text()
            require(not re.search(r'\b(?:sorry|admit|unsafe|native_decide)\b|^\s*axiom\s', code, re.M),
                    'forbidden proof escape: ' + filename)
            names = re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)', code, re.M)
            require(names, 'missing declarations')
            declarations[filename] = [namespace+'.'+name for name in names]
            receipt['sources'][filename] = sha(code.encode())
            (out / filename).write_bytes((HERE / filename).read_bytes())
        audit = ''.join('import '+Path(f).stem+'\n' for f in sources)
        audit += 'set_option pp.universes false\n'
        audit += '\n'.join('#check @'+name+'\n#print axioms '+name
                           for names in declarations.values() for name in names)+'\n'
        (out / 'Checks.lean').write_text(audit)
        env = os.environ.copy()
        env['LEAN_PATH'] = os.pathsep.join([str(out)] + libs)
        (out/'tmp').mkdir()
        env['TMPDIR'] = str(out/'tmp')
        receipt['environment'] = {'LEAN_PATH': env['LEAN_PATH'], 'TMPDIR': env['TMPDIR']}
        steps = [('support', ['-o', 'T088P133.olean', 'T088P133.lean']),
                 ('controls', ['-o', 'Controls.olean', 'Controls.lean']),
                 ('types-axioms', ['Checks.lean'])]
        for label, argv in steps:
            cmd = [str(args.lean), *argv]
            r = subprocess.run(cmd, cwd=out, env=env, capture_output=True, text=True)
            text = r.stdout+r.stderr
            (out/(label+'.log')).write_text(text)
            receipt['runs'].append({'step': label, 'command': cmd, 'cwd': str(out),
                                   'exit_code': r.returncode, 'output_sha256': sha(text.encode())})
            require(r.returncode == 0 and not re.search(r'\b(?:error|warning):', text), 'compile failed/warned: '+label)
        text = (out/'types-axioms.log').read_text()
        reports = {}
        for names in declarations.values():
            for name in names:
                match = re.search("'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",text)
                if match:
                    axioms = set(re.split(r',\s*', re.sub(r'\.\{[^}]*\}', '',match.group(1)).strip()))-{''}
                else:
                    require("'"+name+"' does not depend on any axioms" in text,'missing axiom report: '+name)
                    axioms = set()
                require(axioms <= STANDARD, 'unexpected axiom dependency: '+name)
                reports[name] = sorted(axioms)
        receipt['kernel_dependencies'] = reports
        receipt['declarations'] = declarations
        receipt['status'] = 'COMPILED_SCOPED_SUPPORT_AND_CONTROLS_STANDARD_AXIOMS_ONLY'
        print(receipt['status'])
        print({f: len(names) for f,names in declarations.items()})
    except Exception as error:
        receipt.update(status='FAILED',error=str(error))
        raise
    finally:
        (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')

if __name__ == '__main__':
    main()
