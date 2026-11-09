"""Hash and seal only the assigned review artifacts; no research execution."""
from pathlib import Path
import hashlib
import json
import datetime

ROOT = Path('/home/mj-kang/Documents/Dev/math/factoring-research')
OUT = ROOT / 'research/findings/W032-sweep-assay-audit-evidence'
REPORT = ROOT / 'research/findings/W032-sweep-assay-audit.md'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def write_json(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')

manifest = json.loads((OUT / 'input-manifest.json').read_text())
rows = []
for entry in manifest['files']:
    snapshot = ROOT / entry['snapshot']
    source = ROOT / entry['source']
    rows.append({'source': entry['source'],
                 'snapshot_unchanged': sha(snapshot) == entry['sha256'] and snapshot.stat().st_size == entry['bytes'],
                 'live_source_sha256': sha(source) if source.is_file() else None,
                 'live_source_unchanged': source.is_file() and sha(source) == entry['sha256']})
assert all(r['snapshot_unchanged'] for r in rows), 'Audit input snapshot changed'
write_json(OUT / 'input-stability.json', {
    'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'scope': 'File integrity only. Findings refer to frozen inputs; live drift does not alter them.',
    'files': rows, 'all_snapshots_unchanged': True,
    'live_changes': [r['source'] for r in rows if not r['live_source_unchanged']]})
excluded = {OUT / 'delivery-manifest.json', OUT / 'terminal-manifest.sha256'}
payloads = [REPORT] + sorted(p for p in OUT.rglob('*') if p.is_file() and p not in excluded)
entries = [{'path': str(p.relative_to(ROOT)), 'bytes': p.stat().st_size, 'sha256': sha(p)} for p in payloads]
write_json(OUT / 'delivery-manifest.json', {
    'schema': 'W032-sweep-assay-audit-delivery-v1',
    'sealed_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'project_root': str(ROOT), 'payload_count': len(entries), 'files': entries,
    'exclusions': sorted(str(p.relative_to(ROOT)) for p in excluded),
    'scope': 'Complete assigned report and review evidence, including every frozen nested source manifest and sidecar. No candidate code executed by this audit.'})
digest = sha(OUT / 'delivery-manifest.json')
with (OUT / 'terminal-manifest.sha256').open('x') as stream:
    stream.write(digest + '  delivery-manifest.json\n')
for entry in entries:
    path = ROOT / entry['path']
    assert sha(path) == entry['sha256'] and path.stat().st_size == entry['bytes']
actual = {str(p.relative_to(ROOT)) for p in OUT.rglob('*') if p.is_file()} | {str(REPORT.relative_to(ROOT))}
assert actual == {r['path'] for r in entries} | {str(p.relative_to(ROOT)) for p in excluded}
print(json.dumps({'payloads': len(entries), 'delivery_manifest_sha256': digest,
                  'all_payloads_verified': True, 'complete_file_set': True,
                  'live_input_changes': [r['source'] for r in rows if not r['live_source_unchanged']]}))
