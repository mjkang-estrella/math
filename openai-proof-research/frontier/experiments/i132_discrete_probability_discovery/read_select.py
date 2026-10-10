"""Acquisition-only selector; never executed by verifier."""
import json,sys,runpy
from pathlib import Path
sel=json.loads(Path('frontier/sources/i132_discrete_probability_discovery/selected-inventory.json').read_text())
root,suffix,a,z=sys.argv[1:]
rows=[r for r in sel if r['path'].split('/')[1].startswith(root) and r['path'].endswith(suffix)]
assert len(rows)==1,[r['path'] for r in rows]
sys.argv=['read.py',rows[0]['local'],a,z]
runpy.run_path('frontier/experiments/i132_discrete_probability_discovery/read.py')
