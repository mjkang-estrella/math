#!/usr/bin/env python3
"""Optional fresh author+independent Lean audit on disposable copies. Myeongjin Kang 2026; MIT."""
import argparse
import contextlib
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import types
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import release_common as c

COMPILER_COMMIT = '5045d0056413266e57c625dcd7c365b10e377c52'
MATHLIB = 'd13f23b723b8a846827a245b89c10fc7d3f11612'


def setup(root, lean, cache):
    rows = c.frozen_selection(root)
    lock = c.decode(c.selected(root, c.FORMAL + '/lake-manifest.json'))
    c.require(len(lock['packages']) == 9, 'Expected all nine dependency pins')
    revs, libs = {}, []
    for p in lock['packages']:
        c.require(len(c.name(p['name']).parts) == 1 and p['type'] == 'git', 'Invalid dependency entry')
        repo = cache / p['name']
        actual = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
        c.require(actual == p['rev'], 'Dependency pin differs: ' + p['name'])
        c.require(p['name'] not in revs, 'Duplicate dependency')
        revs[p['name']] = actual
        lib = repo / '.lake/build/lib/lean'
        if lib.is_dir():
            libs.append(str(lib.resolve()))
    c.require(revs['mathlib'] == MATHLIB and
              (cache / 'mathlib/.lake/build/lib/lean').is_dir(), 'Pinned compiled mathlib cache missing')
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    c.require('4.34.1' in version and COMPILER_COMMIT in version, 'Wrong compiler version/commit')
    return rows, {'lean_version': version, 'compiler_sha256': c.sha(lean.read_bytes()),
                  'dependency_revisions': revs, 'dependency_search_paths': libs,
                  'trust': 'Existing compiler and dependency oleans; HEAD pins do not attest cached olean content; no dependency rebuild'}


def copied_runner(review, lean, cache):
    # Execute exactly the audited runner bytes, then override its two documented
    # module defaults in memory. Its CLI has NO --cache/--lean arguments.
    script = review / 'run_review.py'
    module = types.ModuleType('_staircase_disposable_review')
    module.__file__ = str(script)
    exec(compile(script.read_bytes(), str(script), 'exec'), module.__dict__)
    module.LEAN = lean
    module.CACHE = cache
    c.require(module.HERE == review and module.main.__globals__['CACHE'] == cache and
              module.main.__globals__['LEAN'] == lean, 'Disposable runner path setup failed')
    return module


def rebuild(root, lean, cache, check_setup=False):
    lean, cache = lean.absolute(), cache.absolute()
    rows, info = setup(root, lean, cache)
    with tempfile.TemporaryDirectory(prefix='.lean-copy-', dir=c.HERE) as d:
        work = Path(d)
        for path in rows:
            if path.startswith(c.FORMAL + '/') or path.startswith(c.FORMAL_REVIEW + '/'):
                target = work / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(c.selected(root, path))
        author = work / c.FORMAL
        review = work / c.FORMAL_REVIEW
        runner = copied_runner(review, lean, cache)
        info['portable_runner_path_setup'] = 'PASS: exact copied run_review.py with HERE in disposable review, LEAN/CACHE overridden in function globals'
        if check_setup:
            return dict(info, status='PASS: prerequisites and disposable path setup only', fresh_lean_compilation=False)
        proc = subprocess.run([sys.executable, '-I', str(author / 'rebuild.py'),
                               '--lean', str(lean), '--cache', str(cache)], cwd=author,
                              capture_output=True, text=True, timeout=1200)
        c.require(proc.returncode == 0, 'Author rebuild failed: ' + proc.stdout + proc.stderr)
        out = io.StringIO()
        previous_argv = sys.argv
        try:
            sys.argv = [str(review / 'run_review.py')]
            with contextlib.redirect_stdout(out):
                runner.main()
        finally:
            sys.argv = previous_argv
        receipt = c.decode((review / 'audit-receipt.json').read_bytes())
        c.require(receipt['status'] == 'PASS' and len(receipt['runs']) == 8 and
                  all(r['passed'] for r in receipt['runs']), 'Incomplete independent rebuild')
        info.update(status='PASS: fresh author and independent scoped compilation',
                    fresh_lean_compilation=True, author_receipt=c.decode((author / 'validation.json').read_bytes()),
                    independent_receipt=receipt, independent_stdout=out.getvalue(),
                    writes='Disposable copies only; removed, frozen receipts untouched',
                    full_staircase_formalization=False, acceptance_awarded=False)
        return info


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, default=c.ROOT)
    p.add_argument('--lean', type=Path, required=True, help='Existing exact Lean 4.34.1 executable')
    p.add_argument('--cache', type=Path, required=True, help='Existing pinned .lake/packages, all nine Git checkouts and compiled dependencies')
    p.add_argument('--check-setup', action='store_true', help='Validate pins/compiler/disposable path setup without compilation')
    a = p.parse_args()
    print(c.encode(rebuild(a.root, a.lean, a.cache, a.check_setup)).decode(), end='')
