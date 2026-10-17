#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Exact runner controls; Lean proves the mathematical support separately."""
import json
from checked_run import failed

def main():
    tests = {
        'clean_zero_exit': not failed(0, 'all checks complete', ''),
        'nonzero_exit': failed(1, '', ''),
        'printed_failure_zero_exit': failed(0, 'SOME FAIL', ''),
        'stderr_error_zero_exit': failed(0, '', 'error: bad proof'),
        'traceback_zero_exit': failed(0, 'Traceback', ''),
        'seed_strict': 3**20 > 2**20*1936,
        'depth18_below_threshold': 3**18 < 2**18*4*20**2,
    }
    if not all(tests.values()):
        raise RuntimeError('Semantic control rejected')
    print(json.dumps({'status':'PASS exact runner and arithmetic controls','checks':tests},sort_keys=True))
if __name__ == '__main__': main()
