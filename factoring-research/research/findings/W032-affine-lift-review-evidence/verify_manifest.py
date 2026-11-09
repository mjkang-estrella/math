"""Administrative integrity verification only; no research algorithm executes."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
manifest_path = evidence / 'manifest.json'
manifest_bytes = manifest_path.read_bytes()
manifest = json.loads(manifest_bytes)
manifest_hash = hashlib.sha256(manifest_bytes).hexdigest()
excluded = {root / p for p in manifest['inventoryExclusions']}
report = root / 'research/findings/W032-affine-lift-review.md'
actual = {p for p in evidence.rglob('*') if p.is_file()} | {report}
listed = {root / row['path'] for row in manifest['payloads']}
assert actual - excluded == listed, 'Payload inventory mismatch'
assert len(listed) == len(manifest['payloads']), 'Duplicate manifest path'
for row in manifest['payloads']:
    p = root / row['path']
    assert p == report or evidence in p.parents, 'Out-of-scope payload'
    data = p.read_bytes()
    assert len(data) == row['bytes'], row['path'] + ': byte count'
    assert hashlib.sha256(data).hexdigest() == row['sha256'], row['path'] + ': hash'
needed = json.loads((evidence / 'needed-inputs.json').read_text())
for row in needed['inputs']:
    data = (root / row['snapshot']).read_bytes()
    assert len(data) == row['bytes'], row['path'] + ': frozen byte count'
    assert hashlib.sha256(data).hexdigest() == row['sha256'], row['path'] + ': frozen hash'
observed = json.loads((evidence / 'observed-later-manifest.json').read_text())
for row in observed['sources']:
    data = (root / row['snapshot']).read_bytes()
    assert len(data) == row['bytes'], row['path'] + ': later byte count'
    assert hashlib.sha256(data).hexdigest() == row['sha256'], row['path'] + ': later hash'
handoff_path = evidence / 'handoff.json'
sidecar_path = evidence / 'terminal-manifest.sha256'
if handoff_path.exists():
    handoff = json.loads(handoff_path.read_text())
    assert handoff['externalterminalSHA256'] == manifest_hash, 'Handoff hash'
if sidecar_path.exists():
    assert sidecar_path.read_text().split()[0] == manifest_hash, 'Terminal sidecar hash'
print(json.dumps({'payloadsVerified': len(listed), 'frozenInputsVerified': len(needed['inputs']), 'laterSnapshotsVerified': len(observed['sources']), 'manifestSHA256': manifest_hash, 'mode': 'File integrity only; no candidate execution'}, indent=2))
