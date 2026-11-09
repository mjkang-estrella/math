"""Seal the final report and resumed artifacts; preserved initial bytes have separate manifests."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[4]
S=ROOT/'frontier/sources/i31_nonconical_no_mcm/resumed'
E=ROOT/'frontier/experiments/i31_nonconical_no_mcm/resumed'
seal=S/'artifact-seal.json';exclude={seal,E/'verification.json'}
paths=[ROOT/'frontier/iterations/i31-nonconical-no-mcm.md']
for folder in [S,E]:paths += [p for p in folder.rglob('*') if p.is_file() and p not in exclude and '__pycache__' not in p.parts]
rows=[dict(path=str(p.relative_to(ROOT)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted(set(paths))]
seal.write_text(json.dumps(dict(scope='I31 resumed author candidate, not independent mathematical acceptance',files=rows,excluded_outputs=['artifact-seal.json itself','experiments resumed/verification.json'],initial_preservation='checked separately against the frozen parent checkpoint and I28 manifest',count_increment=0),indent=2)+'\n')
print(len(rows))
