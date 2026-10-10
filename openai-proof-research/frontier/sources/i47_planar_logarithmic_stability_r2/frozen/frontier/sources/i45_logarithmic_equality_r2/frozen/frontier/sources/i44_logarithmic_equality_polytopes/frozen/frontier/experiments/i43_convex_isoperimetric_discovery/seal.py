#!/usr/bin/env python3
"""Authoring utility, not the read-only verifier; seals only this task's allowed files."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i43_convex_isoperimetric_discovery';E=Path(__file__).resolve().parent
files=[R/'frontier/iterations/i43-convex-isoperimetric-discovery.md']+list(S.rglob('*'))+list(E.rglob('*'))
excluded={S/'artifact-seal.json',E/'verification-output.json'}
rows=[]
for p in sorted(set(files)):
 if p.is_file() and p not in excluded:
  assert '__pycache__' not in p.parts
  rows.append({'path':str(p.relative_to(R)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size})
(S/'artifact-seal.json').write_text(json.dumps({'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','files':rows,'excluded_generated_output':'frontier/experiments/i43_convex_isoperimetric_discovery/verification-output.json'},indent=2)+'\n')
print(len(rows))
