"""Create a deterministic byte seal; run only after intentional artifact edits."""
from pathlib import Path
import hashlib
import json

BASE = Path(__file__).resolve().parents[3]
SRC = BASE / 'frontier/sources/i17_fresh_discovery'
EXP = BASE / 'frontier/experiments/i17_fresh_discovery'
REPORT = BASE / 'frontier/iterations/i17-fresh-discovery.md'
excluded = {SRC / 'artifact-manifest.json', SRC / 'verification.json'}
files = {p for root in (SRC, EXP) for p in root.rglob('*') if p.is_file() and p not in excluded}
files.add(REPORT)
entries = []
for p in sorted(files):
    data = p.read_bytes()
    entries.append(dict(path=str(p.relative_to(BASE)), bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
manifest = dict(schema=1, assumed_revision='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
                exclusions=[str(p.relative_to(BASE)) for p in sorted(excluded)], files=entries)
(SRC / 'artifact-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print('Sealed', len(entries), 'artifacts')
