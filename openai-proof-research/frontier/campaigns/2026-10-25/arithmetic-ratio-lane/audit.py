#!/usr/bin/env python3
"""Replay both Lean sources from text without importing their compiled modules."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parent
PACKAGES = ROOT.parents[1] / '2026-10-14/formal/.lake/packages'
LEAN = Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
SOURCES = [ROOT / 'formal/RealRatios.lean', ROOT / 'formal/ArithmeticRatios.lean']
BANNED = re.compile(r'\b(sorry|admit|axiom|native_decide|unsafe)\b')
texts = [p.read_text() for p in SOURCES]
for path, text in zip(SOURCES, texts):
    if BANNED.search(text):
        raise SystemExit(f'Forbidden token in {path}')
checks = (ROOT / 'formal/Checks.lean').read_text()
combined = '\n'.join(re.sub(r'^import .*\n', '', text, flags=re.M) for text in texts)
combined = 'import Mathlib\n' + combined + '\n' + re.sub(r'^import .*\n', '', checks, flags=re.M)
env = dict(os.environ)
env['LEAN_PATH'] = ':'.join(str(p) for p in sorted(PACKAGES.glob('*/.lake/build/lib/lean')))
proc = subprocess.run([str(LEAN), '-DwarningAsError=true', '--stdin'], input=combined,
                      text=True, capture_output=True, cwd=ROOT, env=env)
(ROOT / 'audit.log').write_text(proc.stdout + proc.stderr)
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", proc.stdout)
no_axioms = re.findall(r"'([^']+)' does not depend on any axioms", proc.stdout)
expected = re.findall(r'^#print axioms (\S+)', checks, re.M)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert proc.returncode == 0, (proc.returncode, proc.stderr, proc.stdout[-4000:])
assert set(expected) == {n for n, _ in reports} | set(no_axioms)
for name, report in reports:
    assert set(report.split(', ')) <= allowed, (name, report)
version = subprocess.check_output([str(LEAN), '--version'], text=True).strip()
result = {
    'status': 'PASS',
    'method': 'Concatenate source texts; import Mathlib only; Lean --stdin with no local olean path',
    'lean': version,
    'mathlib_revision': 'd13f23b723b8a846827a245b89c10fc7d3f11612',
    'warning_as_error': True,
    'declarations_audited': len(expected),
    'allowed_axioms': sorted(allowed),
    'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in SOURCES},
    'theorems': ['ArithmeticRatios.mathdb_375256', 'ArithmeticRatios.mathdb_375257'],
    'scope': 'Every n >= 2 and k >= 1; actual Nat.totient, Dedekind product, and divisor sum',
    'review_limit': 'Implementation self-audit, not an independent reviewer'
}
(ROOT / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
