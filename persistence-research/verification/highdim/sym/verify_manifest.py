#!/usr/bin/env python3
"""Read-only verification of the sealed artifact hashes and result invariants."""
import hashlib
import json
import pathlib
import sys
sys.dont_write_bytecode=True
HERE=pathlib.Path(__file__).resolve().parent
manifest=json.loads((HERE/'manifest.json').read_text())
for name,expected in manifest['sha256'].items():
    got=hashlib.sha256((HERE/name).read_bytes()).hexdigest()
    assert got==expected,('hash mismatch',name)
summary=json.loads((HERE/'summary.json').read_text())
checks=json.loads((HERE/'standalone_checks.json').read_text())
assert checks['checker_sha256']==hashlib.sha256((HERE/'check_sym.py').read_bytes()).hexdigest()
assert len(checks['files'])==summary['standalone']['files']==2906
assert all(r['result']=='PASS' for r in checks['files'].values())
assert len(summary['closed'])+len(summary['BUDGET'])==331
assert summary['certified_members']==[]
assert sum(r['closed'] for r in summary['counts_by_dimension'].values())==len(summary['closed'])
print(json.dumps({'label':'COMPUTED','result':'PASS','artifact_hashes':len(manifest['sha256']),
                  'standalone_PASS':len(checks['files']),'closed':len(summary['closed']),
                  'BUDGET':len(summary['BUDGET']),'certified_members':summary['certified_members']}))
