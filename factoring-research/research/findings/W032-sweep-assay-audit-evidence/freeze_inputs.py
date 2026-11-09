"""Copy audit inputs and hash bytes only; never import or execute assay sources."""
from pathlib import Path
import hashlib
import json
import datetime

ROOT = Path('/home/mj-kang/Documents/Dev/math/factoring-research')
OUT = ROOT / 'research/findings/W032-sweep-assay-audit-evidence'
paths = [ROOT / p for p in [
    'AGENTS.md', 'RESEARCH_TEAM.md', 'RESEARCH_LOOP.md', 'README.md',
    'docs/SPECIFICATION.md', 'research/STATE.md',
    'research/findings/W032-lift-sweep-protocol.md',
    'research/findings/W032-lift-breakpoint-sweep.md',
    'research/findings/W032-lift-sweep-assay.md',
    'research/findings/W032-carry-quotient-review.md',
    'research/findings/W032-lift-sweep-review.md',
    'research/findings/W032-carry-quotient-review-evidence/manifest.json',
    'research/findings/W032-carry-quotient-review-evidence/input-manifest.json',
    'research/findings/W032-lift-sweep-review-evidence/delivery-manifest.json',
    'research/findings/W032-lift-sweep-review-evidence/terminal-manifest.sha256',
]]
paths += sorted(p for p in (ROOT / 'research/findings/W032-lift-sweep-assay-evidence').rglob('*') if p.is_file())
rows = []
for src in paths:
    rel = src.relative_to(ROOT)
    dst = OUT / 'inputs' / rel
    data = src.read_bytes()
    dst.parent.mkdir(parents=True, exist_ok=True)
    with dst.open('xb') as stream:
        stream.write(data)
    assert src.read_bytes() == data, f'Changed during snapshot: {rel}'
    rows.append({'source': str(rel), 'snapshot': str(dst.relative_to(ROOT)),
                 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()})
record = {'kind': 'W032 sweep assay audit frozen inputs',
          'frozen_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'execution': 'Byte copying and hashing only; no candidate imports or execution.',
          'files': rows}
with (OUT / 'input-manifest.json').open('x') as stream:
    json.dump(record, stream, indent=2)
    stream.write('\n')
print(json.dumps({'frozen_files': len(rows), 'total_bytes': sum(r['bytes'] for r in rows)}))
