#!/usr/bin/env python3
"""Review aid for the exact frozen graph; not a Lean parser or semantic proof."""
from pathlib import Path
import hashlib
import json
import re

proposal = Path('research/proposals/W018-query-instruction-graphs.md').read_text()
assert hashlib.sha256(proposal.encode()).hexdigest() == '08b5befa350dcd0d7f4b98932cb59a0ba3faca54683e911265af3b185b48cf26'
expected = [(int(pc), row.split()) for pc, row in
            re.findall(r'^\| (\d+) \| `([^`]+)` \|$', proposal, re.M)]
code = Path('Research/WordQueryCode.lean').read_text()
actual = []
for name in ['commonSkeleton', 'linearBody', 'binaryBody']:
    body = code.split('def '+name+' : Array TemplateInstr := #[', 1)[1].split('\n]', 1)[0]
    lines = [s.strip() for s in body.splitlines() if s.strip()]
    for line in lines:
        row, pc = line.split(' -- ')
        row = re.sub(r'⟨(\d+), by decide⟩', r'\1', row)
        row = row.rstrip(',').replace('.A1', 'A+1').replace('.A2', 'A+2')
        row = row.replace('.', '')
        actual.append((int(pc), row.split()))
assert len(actual) == len(expected) == 139
assert actual == expected
print(json.dumps({'rows_matched': len(actual), 'scope': 'Exact normalized source-row comparison, not a Lean parser', 'verdict': 'PASS'}, indent=2))
