#!/usr/bin/env python3
"""Copyright 2026 Myeongjin Kang. MIT. Expect proof failure for false weakenings.
Compiles truncated copies only; never alters the reviewed Lean source.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
from rebuild import HERE, DEFAULT_LEAN, DEFAULT_CACHE, LEAN_COMMIT


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean', type=Path, default=DEFAULT_LEAN)
    ap.add_argument('--cache', type=Path, default=DEFAULT_CACHE)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    out = (HERE / (args.output or Path('.replays') / ('mutations-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')))).resolve()
    if not out.is_relative_to(HERE) or out == HERE:
        raise ValueError('Output must be a fresh subdirectory of this package')
    out.mkdir(parents=True, exist_ok=False)
    libs=[]
    lock=json.loads((HERE/'lake-manifest.json').read_text())
    for package in lock['packages']:
        dep=args.cache/package['name']
        actual=subprocess.check_output(['git','-C',str(dep),'rev-parse','HEAD'],text=True).strip()
        if actual != package['rev']:
            raise ValueError('Dependency mismatch: '+package['name'])
        lib=dep/'.lake/build/lib/lean'
        if lib.is_dir(): libs.append(str(lib.resolve()))
    version=subprocess.check_output([str(args.lean),'--version'],text=True)
    if '4.34.1' not in version or LEAN_COMMIT not in version:
        raise ValueError('Wrong compiler')
    src=(HERE/'SeymourSupport.lean').read_text()
    cases=[
        ('boundary-extra-unit','boundary_indicators','(haq : a ≤ q)', '(haq : a ≤ q + 1)'),
        ('missing-anchor','aggregate_negative','m - 1 ≤ (S.card : ℤ)', 'm - 2 ≤ (S.card : ℤ)'),
        ('threshold-too-small','fiber_cardinality_strict','(hm : m = n^2 + 2)', '(hm : m = n^2 + 1)'),
        ('nonstrict-pruning','complement_pruning_contradiction','(hGain : M + 2*d < R.card + C.card)', '(hGain : M + 2*d ≤ R.card + C.card)')]
    results=[]
    env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(libs)
    for label, next_name, old, new in cases:
        # Remove the next declaration and its docstring, retaining all earlier proofs.
        cut=src.index('theorem '+next_name)
        cut=src.rfind('/--',0,cut)
        body=src[:cut]
        if body.count(old) != 1:
            raise ValueError('Mutation must have one exact target: '+label)
        body=body.replace(old,new)+'end SeymourSupport\n'
        with tempfile.TemporaryDirectory(prefix='.mutation-',dir=HERE) as td:
            source=Path(td)/'Mutation.lean';source.write_text(body)
            run=subprocess.run([str(args.lean),'Mutation.lean'],cwd=td,env=env,capture_output=True,text=True,timeout=300)
        (out/(label+'.stdout')).write_text(run.stdout)
        (out/(label+'.stderr')).write_text(run.stderr)
        diagnostic=run.stdout+run.stderr
        # Reject transport, parser, import, unknown-name, and type-elaboration failures.
        proof_failure=('omega could not prove' in diagnostic or 'unsolved goals' in diagnostic or 'linarith failed' in diagnostic)
        invalid=('unknown module' in diagnostic or 'unexpected token' in diagnostic or 'Unknown identifier' in diagnostic or 'Type mismatch' in diagnostic or 'Application type mismatch' in diagnostic)
        if run.returncode == 0 or not proof_failure or invalid:
            raise AssertionError('Expected a mathematical proof rejection: '+label+'\n'+diagnostic)
        results.append({'case':label,'status':'EXPECTED_PROOF_REJECTION','exit_code':run.returncode,'mutant_sha256':hashlib.sha256(body.encode()).hexdigest(),'stdout_sha256':hashlib.sha256(run.stdout.encode()).hexdigest()})
    receipt={'status':'PASS four false weakenings rejected by Lean','source_sha256':hashlib.sha256(src.encode()).hexdigest(),'compiler':version.strip(),'cases':results,'full_S2_formalized':False}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(receipt['status'])

if __name__ == '__main__': main()
