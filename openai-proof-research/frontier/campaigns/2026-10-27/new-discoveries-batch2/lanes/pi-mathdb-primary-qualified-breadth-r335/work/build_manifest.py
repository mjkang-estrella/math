from pathlib import Path
import hashlib, json
LANE = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/pi-mathdb-primary-qualified-breadth-r335')
files = []
for p in sorted(LANE.rglob('*')):
    if p.is_file():
        rel = str(p.relative_to(LANE))
        if rel in ('manifest.json', 'verification-receipt.json'):
            continue
        files.append({'path': rel, 'sha256': hashlib.sha256(p.read_bytes()).hexdigest(), 'size': p.stat().st_size})
(LANE / 'manifest.json').write_text(json.dumps({'lane': 'pi-mathdb-primary-qualified-breadth-r335', 'files': files}, indent=2) + '\n')
print('manifest files:', len(files))
