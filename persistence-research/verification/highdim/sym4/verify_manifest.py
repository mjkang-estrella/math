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
expected_files.add('../../../notes/highdim_sym4.md')
assert expected_files==set(manifest['sha256']), 'unsealed or missing artifact'
for name,expected in manifest['sha256'].items():
    got=hashlib.sha256((HERE/name).read_bytes()).hexdigest()
    assert got==expected,('hash mismatch',name)
summary=json.loads((HERE/'summary.json').read_text())
checks=json.loads((HERE/'dual_checks.json').read_text())
assert len(checks['files'])==sum(summary['dual_check_counts']['M'].values())
assert len(checks['files'])==sum(summary['dual_check_counts']['F'].values())
assert all(r[w]['result']=='PASS' for r in checks['files'].values() for w in ('M','F'))
for who,checker in {'M':HERE.parent/'sym/check_sym.py','F':HERE.parents[1]/'indep4/check_sym_F.py'}.items():
    assert checks['checker_hashes'][who]==hashlib.sha256(checker.read_bytes()).hexdigest()
for name, record in checks['files'].items():
    assert all(hashlib.sha256(pathlib.Path(name).read_bytes()).hexdigest()==record[w]['sha256'] for w in ('M','F')), ('changed checked certificate',name)
assignment=json.loads((HERE/'assignment.json').read_text())
assert len(summary['closed'])+len(summary['open'])==len(assignment['configurations'])==134
assert sum(r['closed'] for dims in summary['counts_by_target_dimension'].values() for r in dims.values())==len(summary['closed'])
assert summary['all_assigned_attempted'] and summary['all_open_escalated']
print(json.dumps({'label':'COMPUTED','result':'PASS','artifact_hashes':len(manifest['sha256']),
                  'standalone_PASS':len(checks['files']),'closed':len(summary['closed']),
                  'OPEN':len(summary['open'])}))
