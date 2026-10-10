"""Seal only the three explicitly authorized I29 artifact locations."""
from pathlib import Path
import hashlib,json
S=Path('frontier/sources/i29_common_base_entropy');E=Path('frontier/experiments/i29_common_base_entropy');R=Path('frontier/iterations/i29-common-base-entropy.md')
excluded={S/'artifact-seal.json',S/'verification.json'}
files=sorted({p for root in [S,E] for p in root.rglob('*') if p.is_file() and p not in excluded}|{R})
rows=[{'path':str(p),'bytes':len(p.read_bytes()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in files]
(S/'artifact-seal.json').write_text(json.dumps({'algorithm':'sha256','excluded':list(map(str,sorted(excluded))),'files':rows},indent=2)+'\n');print(len(rows))
