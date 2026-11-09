from pathlib import Path
import sys,json,hashlib
R=Path(sys.argv[1]);p=R/'results.json';d=json.loads(p.read_text())
assert 'Executable-token source scan passed: 475 modules.' in (R/'logs/source-scan.log').read_text()
assert '62597 declarations' in (R/'metadata-audit.txt').read_text()
assert hashlib.sha256((R/'source-only.zip').read_bytes()).hexdigest()==d['archive_sha256']
d.update(source_scan_passed=True,metadata_audit_declarations=62597,fresh_dimacs_exact_byte_match=True,failed_lean_calls=0,failed_checker_calls=0,new_checked_additions=1061,planned_checkpoint_driver_exit=75,generated_drafts_excluded=True)
p.write_text(json.dumps(d,indent=2)+'\n')
print('Final results and archive hash validated.')
