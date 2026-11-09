#!/usr/bin/env python3
"""Read-only verification of the sealed artifact hashes and result invariants."""
import hashlib
import json
import pathlib
import sys
sys.dont_write_bytecode=True
HERE=pathlib.Path(__file__).resolve().parent
manifest=json.loads((HERE/'manifest.json').read_text())
expected_files={str(p.relative_to(HERE)) for p in HERE.rglob('*')
                if p.is_file() and p.name!='manifest.json' and p.suffix not in ('.log','.tmp') and '__pycache__' not in p.parts}
expected_files.add('../../../notes/highdim_sym3.md')
assert expected_files==set(manifest['sha256']), 'unsealed or missing artifact'
for name,expected in manifest['sha256'].items():
    got=hashlib.sha256((HERE/name).read_bytes()).hexdigest()
    assert got==expected,('hash mismatch',name)
summary=json.loads((HERE/'summary.json').read_text())
checks=json.loads((HERE/'standalone_checks.json').read_text())
assert checks['checker_sha256']==hashlib.sha256((HERE/'check_sym.py').read_bytes()).hexdigest()
assert len(checks['files'])==sum(summary['checker_counts'].values())
assert all(r['result']=='PASS' for r in checks['files'].values())
assert all(r['check']['result']==r['independent']['result']=='PASS' for r in checks['files'].values())
assert checks['direct_checker_sha256']==hashlib.sha256((HERE.parent/'sym/check_sym.py').read_bytes()).hexdigest()
assert checks['independent_checker_sha256']==hashlib.sha256((HERE.parent.parent/'indep4/check_sym_F.py').read_bytes()).hexdigest()
for name, record in checks['files'].items():
    assert hashlib.sha256(pathlib.Path(name).read_bytes()).hexdigest()==record['sha256'], ('changed checked certificate',name)
assignment=json.loads((HERE/'assignment.json').read_text())
assert len(summary['closed'])+len(summary['open'])==len(assignment['configurations'])==210
assert sum(r['closed'] for dims in summary['counts_by_target_dimension'].values() for r in dims.values())==len(summary['closed'])
assert summary['all_configurations_attempted'] and summary['all_still_open_configurations_escalated']
print(json.dumps({'label':'COMPUTED','result':'PASS','artifact_hashes':len(manifest['sha256']),
                  'standalone_PASS':len(checks['files']),'closed':len(summary['closed']),
                  'BUDGET':len(summary['open']),'certified_members':summary['members']}))
