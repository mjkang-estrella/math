#!/usr/bin/env python3
"""Seal only this assigned report and its assigned evidence/experiment directories."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i19_fresh_structural_discovery';E=R/'frontier/experiments/i19_fresh_structural_discovery'
files=[R/'frontier/iterations/i19-fresh-structural-discovery.md']
for base in (S,E):files.extend(p for p in base.rglob('*') if p.is_file() and p not in (S/'artifact-seal.json',E/'validation.json') and '__pycache__' not in p.parts)
obj=dict(pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',files={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)})
(S/'artifact-seal.json').write_text(json.dumps(obj,indent=2)+'\n');print(len(obj['files']),'artifacts sealed')
