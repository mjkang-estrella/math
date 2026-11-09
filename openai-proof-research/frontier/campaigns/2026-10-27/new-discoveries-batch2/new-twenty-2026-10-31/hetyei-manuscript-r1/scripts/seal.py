from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent.parent
exclude={'MANIFEST.sha256','logs/seal.log','receipts/seal.json'}
files=[p for p in sorted(R.rglob('*')) if p.is_file() and str(p.relative_to(R)) not in exclude and not str(p.relative_to(R)).startswith('tmp/')]
(R/'MANIFEST.sha256').write_text(''.join(f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(R)}\n' for p in files))
print('Final manifest bound',len(files),'files. Excludes itself, tmp/, and its active seal log/receipt.')
