#!/usr/bin/env python3
"""Fresh disposable support compilation with a pinned existing dependency cache.
Copyright 2026 Myeongjin Kang; MIT. No network and no writes to the input cache.
"""
from pathlib import Path
import argparse
import json
import os
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from release_common import CAMPAIGN, check_freeze, discover_root, read_regular, safe_name, sha

PIN = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
LEAN = '/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
SOURCE = 'f4a419f9af0c2db04a54ac35f4ffcdebdd2db6aa1b246a5444c635357e735629'


def rebuild(root, cache, lean):
    check_freeze(root)
    revision = subprocess.check_output(['git', '-C', str(cache/'mathlib'), 'rev-parse', 'HEAD'],
                                       text=True).strip()
    if revision != PIN:
        raise ValueError('Wrong mathlib cache revision')
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    if '4.34.1' not in version or '5045d0056413266e57c625dcd7c365b10e377c52' not in version:
        raise ValueError('Expected pinned Lean 4.34.1 compiler commit')
    source = read_regular(root, CAMPAIGN+'/kinetic-formal-v1/KineticSupport.lean')
    if sha(source) != SOURCE or re.search(rb'\b(sorry|admit|axiom|unsafe|native_decide)\b', source):
        raise ValueError('Unexpected supporting source')
    lock = json.loads(read_regular(root, CAMPAIGN+'/kinetic-formal-v1/lake-manifest.json'))
    deps = []
    dependency_revisions = {}
    for package in lock['packages']:
        name = package['name']
        if len(safe_name(name).parts) != 1 or package['type'] != 'git':
            raise ValueError('Unsupported dependency lock entry')
        actual = subprocess.check_output(['git', '-C', str(cache/name), 'rev-parse', 'HEAD'],
                                         text=True).strip()
        if actual != package['rev']:
            raise ValueError('Dependency cache revision differs: '+name)
        dependency_revisions[name] = actual
        lib = cache/name/'.lake/build/lib/lean'
        if lib.is_dir():
            deps.append(lib)
    if cache/'mathlib/.lake/build/lib/lean' not in deps:
        raise ValueError('Compiled mathlib cache missing')
    results = []
    with tempfile.TemporaryDirectory(prefix='kinetic-lean-rebuild-') as directory:
        temp = Path(directory)
        (temp/'KineticSupport.lean').write_bytes(source)
        (temp/'Checks.lean').write_bytes(read_regular(root, CAMPAIGN+'/kinetic-formal-v1/Checks.lean'))
        (temp/'TypedAudit.lean').write_bytes(read_regular(root, CAMPAIGN+'/kinetic-formal-review-r1/TypedAudit.lean'))
        env = os.environ.copy()
        env['LEAN_PATH'] = os.pathsep.join([str(temp)]+[str(p.resolve()) for p in deps])
        for name, args, count in [
            ('source', ['-o', 'KineticSupport.olean', 'KineticSupport.lean'], 0),
            ('author-types', ['Checks.lean'], 9),
            ('independent-types', ['TypedAudit.lean'], 14),
        ]:
            run = subprocess.run([str(lean), *args], cwd=temp, env=env,
                                 capture_output=True, text=True, timeout=300)
            output = run.stdout+run.stderr
            if run.returncode != 0 or 'warning:' in output or 'sorryAx' in output:
                raise ValueError('Fresh Lean compilation failed: '+name+'\n'+output)
            rows = re.findall(r'depends on axioms: \[([^\]]*)\]', output)
            if len(rows) != count or any(set(row.split(', ')) -
                                        {'propext', 'Classical.choice', 'Quot.sound'} for row in rows):
                raise ValueError('Unexpected axiom/type report: '+name)
            results.append({'check':name, 'exit_code':0, 'axiom_lists':len(rows),
                            'compiler_output_sha256':sha(output.encode())})
        compiled_sha = sha((temp/'KineticSupport.olean').read_bytes())
    return {'status':'fresh cached-dependency support compilation passed',
            'lean_version':version, 'mathlib_revision':revision, 'source_sha256':SOURCE,
            'dependency_revisions':dependency_revisions,
            'compiled_dependency_caches':[p.parents[3].name for p in deps],
            'fresh_olean_sha256':compiled_sha, 'runs':results,
            'source_theorems':9, 'independent_audit_declarations':14,
            'author_olean_used':False, 'cache_rebuilt':False, 'network_used':False,
            'writes':'disposable temporary copy only',
            'full_kinetic_theorem_formalized':False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path)
    parser.add_argument('--cache', type=Path, required=True, help='existing .lake/packages directory')
    parser.add_argument('--lean', type=Path, default=Path(LEAN))
    args = parser.parse_args()
    root = args.root or discover_root(Path(__file__).resolve().parent)
    print(json.dumps(rebuild(root, args.cache, args.lean), indent=2))
