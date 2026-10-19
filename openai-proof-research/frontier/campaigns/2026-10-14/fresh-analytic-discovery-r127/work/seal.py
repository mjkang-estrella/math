#!/usr/bin/env python3
"""Write packet/MANIFEST.json and root FINAL.json. Artifact sealing only."""
import hashlib
import json
import os
from pathlib import Path

root = Path(__file__).resolve().parents[1]
packet = root/'packet'

def digest(b):
    return hashlib.sha256(b).hexdigest()

files, dirs = {}, ['.']
for base, ds, fs in os.walk(packet, followlinks=False):
    for name in ds + fs:
        q = Path(base)/name
        assert not q.is_symlink(), q
        rel = q.relative_to(packet).as_posix()
        if q.is_dir():
            dirs.append(rel)
        elif rel != 'MANIFEST.json':
            b = q.read_bytes()
            files[rel] = {'bytes': len(b), 'sha256': digest(b)}
manifest = {'files': dict(sorted(files.items())), 'directories': sorted(dirs)}
mbytes = (json.dumps(manifest, indent=1, sort_keys=True) + '\n').encode()
(packet/'MANIFEST.json').write_bytes(mbytes)

pub = packet/'public'
h = lambda n: digest((pub/n).read_bytes())
final = {
    'task': 'analytic r127 T372L127',
    'pin': 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
    'status': 'AUTHOR_FULL_PROOF_NO_INDEPENDENT_GATES',
    'scope_sha256': h('frozen-scope.md'),
    'prefreeze_sha256': h('prefreeze.md'),
    'manifest_sha256': digest(mbytes),
    'proof_files': {n: h(n) for n in ['proof.md', 'transport-calculation.md', 'boundary-calculation.md']},
    'records': {n: h(n) for n in ['consistency-check.md', 'report.md', 'reading-limits.md', 'verify.py']},
    'runner': {
        'initial': 'GPT-6 Astra (high), interrupted by user stop',
        'resumed': 'Factory Droid (Opus 5.5, high)',
    },
    'postfreeze_changes': 'boundary-layer calculation and Lin-Nakamura read (initial runner); proof.md Section 9 clarifications and consistency-check.md (resumed runner); frozen bytes unchanged',
    'verdicts': {'correctness': None, 'contribution': None, 'count': None},
    'payload_count': len(files),
    'directory_count': len(dirs),
}
(root/'FINAL.json').write_bytes((json.dumps(final, indent=1, sort_keys=True) + '\n').encode())
print(json.dumps({'manifest_sha256': final['manifest_sha256'],
                  'final_sha256': digest((root/'FINAL.json').read_bytes()),
                  'payloads': len(files), 'directories': len(dirs)}))
