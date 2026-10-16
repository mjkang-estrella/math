#!/usr/bin/env python3
"""MIT, Myeongjin Kang. Read-only review integrity; no proof checker.

Run with python -B -I verify.py --seal-sha256 EXTERNALLY_REPORTED_ANCHOR.
Never executes frozen child, third-party, or historical mathematical code.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import tarfile

ROOT = Path(__file__).resolve().parent
R2_ANCHOR = '92f9d1b04e4631cb436a58b7aeb46c2444f25d63fff50522ea0a7cc155735003'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'


def record(path):
    if path.is_symlink() or not path.is_file():
        raise ValueError('not a regular nonsymlink file: ' + str(path))
    data = path.read_bytes()
    return {'size': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def match(path, expected):
    if record(path) != {k: expected[k] for k in ('size', 'sha256')}:
        raise ValueError('size/hash mismatch: ' + str(path))


def local(root, name):
    relative = Path(name)
    if relative.is_absolute() or '..' in relative.parts or not relative.parts:
        raise ValueError('unsafe path')
    return root / relative


def inventory(root):
    rows = []
    for path in sorted(root.rglob('*')):
        if path.is_symlink():
            raise ValueError('symlink in inventory')
        if path.is_file():
            rows.append({'path': path.relative_to(root).as_posix(), **record(path)})
    return rows


def sealed_tree(root, anchor):
    if record(root / 'seal.json')['sha256'] != anchor:
        raise ValueError('external seal anchor mismatch')
    if (root / 'seal.sha256').read_text() not in (anchor + '\n', anchor + '  seal.json\n'):
        raise ValueError('detached seal mismatch')
    seal = json.loads((root / 'seal.json').read_text())
    if 'manifests' in seal:
        manifests = seal['manifests']
    else:
        manifests = {seal[k]['path']: seal[k] for k in ('inputs', 'outputs')}
    expected = {'seal.json', 'seal.sha256'} | set(manifests)
    for name, info in manifests.items():
        match(local(root, name), info)
        for row in json.loads(local(root, name).read_text())['files']:
            if row['path'] in expected:
                raise ValueError('duplicate manifest member')
            expected.add(row['path'])
            match(local(root, row['path']), row)
    if expected != {row['path'] for row in inventory(root)}:
        raise ValueError('exact membership mismatch: ' + str(root))


def main(anchor):
    sealed_tree(ROOT, anchor)
    before = inventory(ROOT)
    baseline = json.loads((ROOT / 'external-baseline.json').read_text())
    r2 = ROOT.parent / 'artin-root-r2'
    sealed_tree(r2, R2_ANCHOR)
    for tree in json.loads((r2 / 'external-inputs.json').read_text())['trees']:
        sealed_tree(Path(tree['root']), tree['external_seal_sha256'])
    for tree in baseline['trees']:
        if inventory(Path(tree['root'])) != tree['inventory']:
            raise ValueError('frozen external tree changed: ' + tree['root'])
    # Mutable context is represented exclusively by owned byte snapshots.
    # initial_fixed_files is historical before/after evidence, not a replay binding.
    for row in json.loads((ROOT / 'context-snapshots.json').read_text()):
        match(local(ROOT, row['snapshot']), row)
    for row in json.loads((ROOT / 'source-records.json').read_text())['files']:
        path = local(ROOT, row['path']) if row['location'] == 'owned' else Path(row['path'])
        match(path, row)
    records = json.loads((r2 / 'pinned-blobs.json').read_text())
    if records['pin'] != PIN:
        raise ValueError('upstream pin mismatch')
    catalogue = json.loads(Path(records['catalogue']).read_text())
    if catalogue['truncated'] or catalogue['sha'] != 'df0564b2deaab87e07854b6344d8c2f037682e77':
        raise ValueError('complete catalogue identity mismatch')
    blobs = {x['path']: x['sha'] for x in catalogue['tree'] if x['type'] == 'blob'}
    for row in records['retrievals']:
        data = Path(row['external_path']).read_bytes()
        digest = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if digest != row['git_blob_sha1'] or digest != blobs[row['upstream_path']]:
            raise ValueError('Git blob identity mismatch')
        match(Path(row['external_path']), {'size': row['bytes'], 'sha256': row['sha256']})
        if row['url'] != 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + row['upstream_path']:
            raise ValueError('unpinned source URL')
    archive = r2 / 'inputs/private/dgm-2407.07459v2-source.tar'
    provenance = json.loads((r2 / 'dgm-source-provenance.json').read_text())
    match(archive, {'size': provenance['archive_size'], 'sha256': provenance['archive_sha256']})
    with tarfile.open(fileobj=io.BytesIO(archive.read_bytes()), mode='r:*') as handle:
        members = [x for x in handle.getmembers() if x.isfile() and x.name.endswith('.tex')]
        if [x.name for x in members] != provenance['tex_members']:
            raise ValueError('DGM TeX membership mismatch')
        for i, member in enumerate(members):
            if handle.extractfile(member).read() != (r2 / ('inputs/private/dgm-source-' + str(i) + '.tex')).read_bytes():
                raise ValueError('DGM TeX extraction mismatch')
    if (r2 / 'original-scope.md').read_bytes() != (ROOT.parent / 'fresh-structural-discovery-r11/original-scope.md').read_bytes():
        raise ValueError('changed scope')
    for tree in baseline['trees']:
        if inventory(Path(tree['root'])) != tree['inventory']:
            raise ValueError('external tree changed during verification')
    if inventory(ROOT) != before:
        raise ValueError('review tree changed during verification')
    result = {
        'status': 'PASS_REVIEW_INTEGRITY_ONLY',
        'external_frozen_tree_files': sum(len(t['inventory']) for t in baseline['trees']),
        'pinned_git_blobs': len(records['retrievals']),
        'historical_ledger_snapshot': True,
        'live_ledger_or_parent_directory_binding': False,
        'stored_child_or_third_party_code_executed': False,
        'writes': False,
        'mathematics_checked_by_code': False,
    }
    if result != json.loads((ROOT / 'verification-receipt.json').read_text()):
        raise ValueError('immutable receipt mismatch')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--seal-sha256', required=True)
    arguments = parser.parse_args()
    try:
        main(arguments.seal_sha256)
    except Exception as error:
        print(json.dumps({'status': 'REJECT', 'error': str(error), 'writes': False}, sort_keys=True))
        raise SystemExit(1)
