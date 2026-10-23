#!/usr/bin/env python3
"""Verify the completed packet without assigning a mathematical gate."""
from pathlib import Path
import hashlib
import json
import subprocess

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'discovery-arithmetic-r162j-parent'
r = b / 'fresh-arithmetic-discovery-r162j'
m = r / 'packet/private'
sha = lambda data: hashlib.sha256(data).hexdigest()
load = lambda path: json.loads(path.read_bytes())
anchors = {
    'packet/FINAL.md': '4a14d880ec0959ce77e9daa74cdecf32c18375e2e42bde7b7d81370cd760bc8b',
    'MANIFEST.json': 'b5e0f4aa0836114ecd5a98a7689bb3828e8cc11321b9b9074d608eaab2aa283a',
    'REPORT.md': 'bbfc7b604b20a6c388bd5d137531a7e0008019d0e978a46b52adebbc244b45b3',
}
for rel, digest in anchors.items():
    assert sha((r / rel).read_bytes()) == digest
checked = subprocess.run([
    'python', '-I', '-B', str(r / 'packet/verify_packet.py'), '--root', str(r),
    '--final-sha256', anchors['packet/FINAL.md'],
    '--manifest-sha256', anchors['MANIFEST.json'],
    '--report-sha256', anchors['REPORT.md'],
], check=True, text=True, capture_output=True)
manifest = load(r / 'MANIFEST.json')
assert len(manifest['files']) == 91
tree_data = (p / 'sources/preprints-tree.json').read_bytes()
assert sha(tree_data) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = json.loads(tree_data)
assert len(tree['tree']) == 13223 and not tree['truncated']
by_path = {x['path']: x for x in tree['tree']}
auth = load(m / 'canonical-authentication.json')
assert len(auth) == 35
for e in auth:
    original = by_path[e['path']]
    assert all(e[k] == original[k] for k in ['path', 'mode', 'type', 'sha', 'size'])
    data = (p / e['local']).read_bytes()
    assert len(data) == e['size'] and sha(data) == e['sha256']
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == e['sha']
direct = load(m / 'direct-reading.json')
for e in direct:
    data = (p / e['path']).read_bytes()
    if 'extent' in e:
        data = data[slice(*e['extent'])]
    else:
        assert len(data) == e['bytes']
    assert sha(data) == e['sha256']
history = load(m / 'history-reading.json')
for e in history:
    data = (p / e['path']).read_bytes()
    assert sha(data) == e['whole_sha256']
    assert sha(data[e['start']:e['end']]) == e['span_sha256']
primary = load(m / 'primary-reading.json')
for e in primary:
    data = (m / 'primary' / e['local']).read_bytes()
    assert len(data) == e['bytes'] and sha(data) == e['sha256']
controls = load(m / 'controls/results.json')['results']
assert len(controls) == 5
assert all(x['expected_exit'] == x['actual_exit'] for x in controls)
before = load(o / 'private/root-before.json')
after = {f.relative_to(r).as_posix(): {
    'bytes': f.stat().st_size, 'mode': f.stat().st_mode, 'sha256': sha(f.read_bytes())
} for f in r.rglob('*') if f.is_file()}
assert before == after
result = {
    'status': 'MATCH', 'anchors': anchors, 'read_only_verifier_stdout': checked.stdout,
    'payload_files': 91, 'payload_bytes': sum(x['bytes'] for x in manifest['files']),
    'canonical_blobs_against_complete_tree': 35, 'canonical_bytes': sum(x['size'] for x in auth),
    'completed_original_whole_comparisons': 4, 'direct_instruction_span_comparisons': 3,
    'original_history_whole_and_span_comparisons': len(history),
    'primary_text_binding_comparisons': len(primary),
    'copied_controls_observed_not_rerun': len(controls),
    'saved_control_outcomes_match_expectations': True, 'controls_rerun': False,
    'entire_completed_root_unchanged_files': len(after),
    'parent_semantically_read': ['REPORT.md', 'packet/FINAL.md', 'packet/NOTES.md',
                                 'packet/PREFREEZE.md', 'packet/verify_packet.py',
                                 'packet/private/READING-ISOLATION.md'],
    'parent_canonical_or_primary_mathematics_reread': False,
    'author_canonical_semantic_text_bytes_reported': 265136,
    'canonical_text_total_bytes': 1019669,
    'complete_operative_proof_reading_objective': 'NOT_ATTAINED',
    'verification_recovery': 'Initial parent run stopped on the nested control-results schema; exact saved metadata was read and the results member checked. Author bytes unchanged.',
    'mathematical_gate': False, 'count_change': 0,
}
(o / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
