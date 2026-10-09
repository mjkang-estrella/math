"""Provenance and exact-constant bookkeeping; not a numerical proof test."""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / 'frontier/sources/i11_capacity_r4'
manifest = json.loads((BASE / 'input-manifest.json').read_text())

def digest(data):
    return hashlib.sha256(data).hexdigest()

inventory = json.loads((ROOT / 'sources/preprints-tree.json').read_text())
assert inventory['truncated'] is False
entries = {e['path']: e for e in inventory['tree']}
observations = []
for rec in manifest['inputs']:
    current = (ROOT / rec['path']).read_bytes()
    same = digest(current) == rec['sha256']
    live = 'novelty-r3.md' in rec['path']
    if not live:
        assert same, ('audited input changed', rec['path'])
    if 'snapshot' in rec:
        snapshot = (ROOT / rec['snapshot']).read_bytes()
        assert digest(snapshot) == rec['sha256']
        assert len(snapshot) == rec['bytes']
    observations.append({'path': rec['path'], 'unchanged': same,
                         'current_sha256': digest(current),
                         'live_draft_context_only': live})
for rec in manifest['sources']:
    data = (ROOT / rec['stored']).read_bytes()
    assert len(data) == rec['bytes']
    assert digest(data) == rec['sha256']
    blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    assert blob == rec['git_blob'] == entries[rec['upstream_path']]['sha']
K = F(1, 3000)
kappa = 2*K/(1+9*K)**3
loss_first = (2000 + 2*2000**2)*F(1, 10**8)
# sqrt(3)>1 gives the strict rational upper bound for the second term.
loss_upper = loss_first + F(1, 750)
assert 3*K == F(1, 1000)
assert kappa == F(2000000, 3027081081)
assert loss_upper == F(12203, 150000) < F(1, 2)
artifact_path = BASE / 'artifact-manifest.json'
artifact_count = 0
if artifact_path.exists():
    for rec in json.loads(artifact_path.read_text())['artifacts']:
        data = (ROOT / rec['path']).read_bytes()
        assert digest(data) == rec['sha256'], rec['path']
        assert len(data) == rec['bytes'], rec['path']
        artifact_count += 1
print(json.dumps({'status': 'PASS', 'purpose': 'Provenance and constant bookkeeping only; universal proof is in the review.',
                  'pin': manifest['pin'], 'inventory_entries': len(entries),
                  'source_files_verified': len(manifest['sources']),
                  'kappa': str(kappa), 'strict_loss_upper_bound': str(loss_upper),
                  'input_observations': observations,
                  'artifact_files_verified': artifact_count}, indent=2))
