#!/usr/bin/env python3
"""Parent provenance and copied integrity checks, never a proof gate."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

REPO = Path(__file__).resolve().parents[4]
BASE = REPO / 'frontier/campaigns/2026-10-14'
ANCHORS = {
    'fresh-structural-discovery-r107': ('manifest.json', '7301caa2a4eb6b6bed90c087de40a8a5e74e57d62b369ae39e5d09e2b63940fc'),
    'fresh-arithmetic-discovery-r71': ('MANIFEST.json', '74c4f4b5e1267556b0ef4342aa55f5375054820115bd38a76c7d549b1f6147d6'),
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    tree = json.loads((REPO / 'sources/preprints-tree.json').read_text())
    assert len(tree['tree']) == 13223 and tree['truncated'] is False
    blobs = {x['path']: x['sha'] for x in tree['tree'] if x['type'] == 'blob'}
    results = {}
    for name, (manifest, anchor) in ANCHORS.items():
        root = BASE / name
        assert sha(root / manifest) == anchor
        receipts = json.loads((root / 'source-receipts.json').read_text())
        records = receipts.get('records', receipts.get('source_files'))
        matched = 0
        for rec in records:
            if rec.get('success') is False:
                continue
            data = (root / rec.get('local', rec.get('retained_path'))).read_bytes()
            blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
            assert blob == rec['git_blob'] == blobs[rec['path']]
            assert hashlib.sha256(data).hexdigest() == rec['sha256']
            matched += 1
        results[name] = {'anchor': anchor, 'canonical_source_blobs_matched': matched}

    root = BASE / 'fresh-arithmetic-discovery-r71'
    author = json.loads((root / 'author-input-receipts.json').read_text())['files']
    for rec in author:
        assert sha(REPO / rec['path']) == rec['sha256']
    results[root.name]['author_input_receipts_matched'] = len(author)

    root = BASE / 'fresh-structural-discovery-r107'
    anchor = ANCHORS[root.name][1]
    controls = []
    reasons = {
        'clean': '', 'wrong_anchor': 'external manifest anchor mismatch',
        'changed_payload': 'payload mismatch', 'missing_payload': 'No such file',
        'extra_file': 'public membership mismatch',
        'symlink_payload': 'not a single-link regular file',
        'hardlink_payload': 'not a single-link regular file',
        'changed_manifest': 'external manifest anchor mismatch',
    }
    with tempfile.TemporaryDirectory(prefix='structural-r107-parent-', dir='/var/tmp') as temp:
        temp = Path(temp)
        for case, reason in reasons.items():
            fixture = temp / case
            fixture.mkdir()
            for src in root.iterdir():
                if src.is_file():
                    shutil.copyfile(src, fixture / src.name)
            target = fixture / 'frame-obstruction.md'
            used_anchor = anchor
            if case == 'wrong_anchor':
                used_anchor = '0' * 64
            elif case == 'changed_payload':
                target.write_bytes(target.read_bytes() + b'\nMUTATION\n')
            elif case == 'missing_payload':
                target.unlink()
            elif case == 'extra_file':
                (fixture / 'extra.txt').write_text('MUTATION')
            elif case == 'symlink_payload':
                target.unlink()
                target.symlink_to(fixture / 'README.md')
            elif case == 'hardlink_payload':
                twin = temp / 'hardlink-twin'
                shutil.copyfile(target, twin)
                target.unlink()
                os.link(twin, target)
            elif case == 'changed_manifest':
                target = fixture / 'manifest.json'
                target.write_bytes(target.read_bytes() + b' ')
            run = subprocess.run([sys.executable, '-I', '-B', str(root / 'verify.py'),
                                  '--root', str(fixture), '--anchor', used_anchor],
                                 text=True, capture_output=True)
            assert (run.returncode == 0) == (case == 'clean'), (case, run.stdout, run.stderr)
            assert reason in run.stderr, (case, run.stderr)
            controls.append({'case': case, 'accepted': run.returncode == 0,
                             'expected_reason_matched': True})
    results['fresh-structural-discovery-r107']['copied_integrity_controls'] = controls
    for name, (manifest, anchor) in ANCHORS.items():
        assert sha(BASE / name / manifest) == anchor
    print(json.dumps({'status': 'PASS_PROVENANCE_AND_COPIED_INTEGRITY_ONLY',
                      'complete_tree_entries': len(tree['tree']), 'results': results,
                      'mathematical_proof_gate': False, 'count_change': 0}, indent=2))

if __name__ == '__main__':
    main()
