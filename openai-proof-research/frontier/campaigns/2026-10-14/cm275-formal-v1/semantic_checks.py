#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Actual Lean false-goal controls and actual zero-exit failure-marker rejection.
These are counterexample tests, not independent verification of CM275.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from checked_run import run_checked

HERE = Path(__file__).resolve().parent

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', required=True, type=Path)
    args = ap.parse_args()
    out = args.output.resolve()
    if not out.is_relative_to(HERE):
        raise ValueError('Outputs must remain inside assigned package')
    out.mkdir(parents=True, exist_ok=False)
    lean = os.environ['CM275_LEAN']
    expected = ['01_duplicate_modes.lean','02_centered_alias.lean','03_nonunit_phase.lean',
                '04_missing_sign.lean','05_noncharacter_weight.lean','06_missing_subnormalization.lean',
                '07_missing_nonnegative_probability.lean','08_wrong_margin.lean',
                '09_missing_approximation_loss.lean']
    paths = sorted((HERE/'mutants').glob('*.lean'))
    if [p.name for p in paths] != expected:
        raise ValueError('Exact nine mutant filenames required')
    rows = []
    for path in paths:
        result = subprocess.run([lean,str(path)],capture_output=True,text=True)
        (out/(path.stem+'.stdout')).write_text(result.stdout)
        (out/(path.stem+'.stderr')).write_text(result.stderr)
        transcript = result.stdout + result.stderr
        if result.returncode == 0 or not ('unsolved goals' in transcript or 'proved that the proposition' in transcript):
            raise ValueError('Mutant did not fail at its mathematical proof goal: '+path.name)
        if any(s in transcript for s in ['unknown identifier','Unknown identifier','unknown module','unexpected token','Invalid field','Invalid argument']):
            raise ValueError('Malformed rather than mathematical mutant: '+path.name)
        rows.append({'name':path.name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                     'exit_code':result.returncode,'reason':'false mathematical proof goal rejected'})
    executed_mutants = len(rows)
    env = os.environ.copy()
    for name, code in [('zero-exit-printed-failure',"print('SOME FAIL')"),
                       ('zero-exit-stderr-error',"import sys; print('error: deliberate',file=sys.stderr)"),
                       ('nonzero-exit',"raise SystemExit(7)")]:
        try:
            run_checked([sys.executable,'-c',code],Path.cwd(),env,out/name)
        except RuntimeError:
            rows.append({'name':name,'actual_wrapper_rejected':True})
        else:
            raise ValueError('Actual wrapper accepted '+name)
    clean = run_checked([sys.executable,'-c',"print('clean child')"],Path.cwd(),env,out/'clean-child')
    rows.append({'name':'clean-child','actual_wrapper_accepted':clean.returncode==0})
    receipt={'result':'PASS_SCOPED_CONTROLS','mutants':executed_mutants,'wrapper_controls':len(rows)-executed_mutants,'rows':rows,
             'mathematical_full_theorem_certified':False}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,sort_keys=True))
if __name__=='__main__':
    main()
