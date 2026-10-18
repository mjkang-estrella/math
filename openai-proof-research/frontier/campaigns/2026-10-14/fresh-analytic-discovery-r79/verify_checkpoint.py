#!/usr/bin/env python3
"""Identity/status verifier for a no-nominee research checkpoint, not a proof checker."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath

def digest(data):
    return hashlib.sha256(data).hexdigest()

def verify(packet, repo, source_bodies=True):
    manifest = json.loads((packet / 'MANIFEST.json').read_text())
    assert manifest['status'] == 'SEALED_NO_NOMINEE', 'status'
    assert manifest['full_target_proved'] is False, 'full-target flag'
    assert manifest['accepted'] is False and manifest['published'] is False, 'release flags'
    assert manifest['count_change'] == 0, 'count'
    expected = manifest['files']
    actual = {x.relative_to(packet).as_posix() for x in packet.rglob('*')
              if x.is_file() and 'private' not in x.relative_to(packet).parts
              and '__pycache__' not in x.relative_to(packet).parts
              and x.name != 'MANIFEST.json'}
    assert actual == set(expected), 'public file set'
    for name, identity in expected.items():
        path = PurePosixPath(name)
        assert not path.is_absolute() and '..' not in path.parts, 'unsafe path'
        target = packet / name
        assert not target.is_symlink(), 'symlink'
        data = target.read_bytes()
        assert len(data) == identity['bytes'] and digest(data) == identity['sha256'], 'public identity: ' + name
    scope = json.loads((packet / 'scope-status.json').read_text())
    assert scope['target_frozen'] is False and scope['full_result_claimed'] is False, 'scope flags'
    tree_bytes = (repo / 'sources/preprints-tree.json').read_bytes()
    assert digest(tree_bytes) == manifest['canonical_tree_sha256'], 'canonical tree anchor'
    tree = json.loads(tree_bytes)
    assert tree['truncated'] is False, 'truncated tree'
    blobs = {x['path']: x['sha'] for x in tree['tree']}
    receipts = json.loads((packet / 'source-receipts.json').read_text())
    assert receipts['pin'] == manifest['pin'] == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb', 'pin'
    assert len(receipts['files']) == 27, 'source count'
    for item in receipts['files']:
        assert blobs[item['path']] == item['git_blob'], 'canonical membership'
        if source_bodies:
            data = (packet / item['local']).read_bytes()
            blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
            assert blob == item['git_blob'] and digest(data) == item['sha256'], 'source body'
            assert len(data) == item['bytes'], 'source size'
    primary = json.loads((packet / 'primary-receipts.json').read_text())[0]
    assert primary['version'] == 'arXiv:2505.09037v2', 'primary version'
    if source_bodies:
        data = (packet / 'private/primary/demeter-wu-v2.pdf').read_bytes()
        assert digest(data) == primary['sha256'] and len(data) == primary['bytes'], 'primary identity'
    return {'status': 'IDENTITY_AND_STATUS_PASS', 'public_files': len(expected),
            'canonical_source_receipts': 27, 'private_bodies_checked': source_bodies,
            'mathematical_review': False, 'full_target_proved': False, 'count_change': 0}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--receipts-only', action='store_true')
    args = parser.parse_args()
    print(json.dumps(verify(args.packet, args.repo, not args.receipts_only), sort_keys=True))
