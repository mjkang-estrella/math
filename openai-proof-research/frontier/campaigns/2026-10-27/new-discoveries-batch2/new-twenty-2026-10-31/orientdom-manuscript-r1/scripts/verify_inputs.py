from pathlib import Path
import hashlib,json
R=Path.cwd(); before=json.loads((R/'inputs-before.json').read_text())
def entry(p): return dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
after={p:entry(R.parent/p) for p in before}; copies={p:entry(R/'inputs'/p) for p in before}
assert before==after,'Frozen sibling inputs changed'
assert before==copies,'Source snapshots differ'
(R/'inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
(R/'receipts/input-integrity.json').write_text(json.dumps(dict(status='PASS',frozen_files=len(before),before_after_equal=True,copies_identical=True),indent=2)+'\n')
print('PASS:',len(before),'original input files unchanged; all snapshot bytes identical')
