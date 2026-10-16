#!/usr/bin/env python3
"""MIT, Myeongjin Kang. Read-only authentication; no mathematical verdict."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import re
import tarfile

ROOT = Path(__file__).resolve().parent


def digest(p):
    b = p.read_bytes()
    return {'size': len(b), 'sha256': hashlib.sha256(b).hexdigest()}


def inventory(root):
    rows = []
    for p in sorted(root.rglob('*')):
        if p.is_symlink():
            raise ValueError('symlink forbidden: ' + str(p))
        if p.is_file():
            rows.append({'path': p.relative_to(root).as_posix(), **digest(p)})
    return rows


def safe(root, name):
    q = Path(name)
    if q.is_absolute() or '..' in q.parts or not q.parts:
        raise ValueError('unsafe inventory member')
    p = root / q
    if not p.resolve().is_relative_to(root.resolve()):
        raise ValueError('inventory escape')
    return p


def match(p, row):
    if digest(p) != {k: row[k] for k in ('size', 'sha256')}:
        raise ValueError('size/hash mismatch: ' + str(p))


def authenticate_tree(root, anchor, before):
    if digest(root / 'seal.json')['sha256'] != anchor:
        raise ValueError('external seal anchor mismatch')
    if (root / 'seal.sha256').read_text() not in (
            anchor + '\n', anchor + '  seal.json\n'):
        raise ValueError('detached seal mismatch')
    seal = json.loads((root / 'seal.json').read_text())
    if set(seal['manifests']) != {'inputs-manifest.json', 'outputs-manifest.json'}:
        raise ValueError('manifest-set mismatch')
    expected = {'seal.json', 'seal.sha256', 'inputs-manifest.json', 'outputs-manifest.json'}
    counts = {}
    for name, receipt in seal['manifests'].items():
        match(safe(root, name), receipt)
        entries = json.loads((root / name).read_text())['files']
        counts[name] = len(entries)
        for row in entries:
            if row['path'] in expected:
                raise ValueError('duplicate inventory member')
            expected.add(row['path'])
            match(safe(root, row['path']), row)
    if expected != {r['path'] for r in before}:
        raise ValueError('exact tree membership mismatch')
    return counts


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seal-sha256', required=True)
    args = parser.parse_args()
    own_before = inventory(ROOT)
    external = json.loads((ROOT / 'external-inputs.json').read_text())
    trees_before = {t['root']: inventory(Path(t['root'])) for t in external['trees']}
    files_before = {r['path']: digest(Path(r['path'])) for r in external['files']}
    error = None
    result = None
    try:
        if not re.fullmatch('[0-9a-f]{64}', args.seal_sha256):
            raise ValueError('malformed external anchor')
        counts = authenticate_tree(ROOT, args.seal_sha256, own_before)
        for t in external['trees']:
            before = trees_before[t['root']]
            if before != t['inventory']:
                raise ValueError('external inventory mismatch: ' + t['root'])
            authenticate_tree(Path(t['root']), t['external_seal_sha256'], before)
        for row in external['files']:
            match(Path(row['path']), row)

        pin = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
        records = json.loads((ROOT / 'pinned-blobs.json').read_text())
        if records['pin'] != pin:
            raise ValueError('upstream revision mismatch')
        catalogue = json.loads(Path(records['catalogue']).read_text())
        if catalogue['truncated'] or catalogue['sha'] != 'df0564b2deaab87e07854b6344d8c2f037682e77':
            raise ValueError('complete catalogue identity mismatch')
        blobs = {x['path']: x['sha'] for x in catalogue['tree'] if x['type'] == 'blob'}
        seen = set()
        for row in records['retrievals']:
            if row['upstream_path'] in seen:
                raise ValueError('duplicate pinned source')
            seen.add(row['upstream_path'])
            b = Path(row['external_path']).read_bytes()
            g = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
            if g != row['git_blob_sha1'] or g != blobs[row['upstream_path']]:
                raise ValueError('pinned Git blob mismatch')
            if len(b) != row['bytes'] or hashlib.sha256(b).hexdigest() != row['sha256']:
                raise ValueError('pinned source receipt mismatch')
            if row['url'] != 'https://raw.githubusercontent.com/openai/math/' + pin + '/' + row['upstream_path']:
                raise ValueError('unpinned raw source URL')

        literature = json.loads((ROOT / 'literature-retrievals.json').read_text())
        if {r['url'] for r in literature} != {
            'https://arxiv.org/html/2407.07459v2', 'https://arxiv.org/html/2502.20711v1'
        }:
            raise ValueError('primary HTML version mismatch')
        for row in literature:
            match(safe(ROOT, row['path']), row)
        source = json.loads((ROOT / 'dgm-source-provenance.json').read_text())
        if source['url'] != 'https://arxiv.org/src/2407.07459v2':
            raise ValueError('DGM source version mismatch')
        archive = ROOT / 'inputs/private/dgm-2407.07459v2-source.tar'
        match(archive, {'size': source['archive_size'], 'sha256': source['archive_sha256']})
        with tarfile.open(fileobj=io.BytesIO(archive.read_bytes()), mode='r:*') as tf:
            members = [m for m in tf.getmembers() if m.isfile() and m.name.endswith('.tex')]
            if [m.name for m in members] != source['tex_members']:
                raise ValueError('DGM source archive TeX membership mismatch')
            for i, member in enumerate(members):
                if tf.extractfile(member).read() != (ROOT / ('inputs/private/dgm-source-' + str(i) + '.tex')).read_bytes():
                    raise ValueError('DGM original TeX extraction mismatch')

        r11 = next(Path(t['root']) for t in external['trees']
                   if t['external_seal_sha256'] == '10fd62265feb74bac5d90b1001346699071e4a80d747b7e6f8ae5df6726c0e5c')
        if (ROOT / 'original-scope.md').read_bytes() != (r11 / 'original-scope.md').read_bytes():
            raise ValueError('original full scope changed')
        status = json.loads((ROOT / 'status.json').read_text())
        if status['status'] != 'PROPOSED_PROOF_FULL_R' or status['accepted_count'] != 4 or status['counted']:
            raise ValueError('disposition mismatch')
        if status['independent_proof_review'] or status['contribution_nomination']:
            raise ValueError('unauthorized independent verdict or nomination')
        auth = json.loads((ROOT / 'verify-preexecution.json').read_text())
        match(ROOT / 'verify.py', auth)

        result = {
            'status': 'PASS_INTEGRITY_ONLY',
            'target_status': 'PROPOSED_PROOF_FULL_R',
            'mathematical_or_contribution_verdict': False,
            'counted': False, 'accepted_count': 4,
            'input_files': counts['inputs-manifest.json'],
            'output_files': counts['outputs-manifest.json'],
            'own_files': len(own_before),
            'external_tree_files': sum(len(v) for v in trees_before.values()),
            'external_fixed_files': len(files_before),
            'pinned_git_blobs': len(records['retrievals']),
            'historical_or_third_party_code_executed': False,
            'frozen_trees_and_fixed_inputs_unchanged': True
        }
        receipt = json.dumps(result, indent=2, sort_keys=True) + '\n'
        if receipt.encode() != (ROOT / 'verification-receipt.json').read_bytes():
            raise ValueError('immutable integrity receipt mismatch')
    except Exception as exc:
        error = str(exc)
    finally:
        if inventory(ROOT) != own_before:
            raise RuntimeError('own tree changed during verification')
        for name, before in trees_before.items():
            if inventory(Path(name)) != before:
                raise RuntimeError('external tree changed during verification: ' + name)
        for name, before in files_before.items():
            if digest(Path(name)) != before:
                raise RuntimeError('external fixed file changed during verification: ' + name)
    if error is not None:
        print(json.dumps({'status': 'REJECT', 'error': error,
                          'frozen_trees_and_fixed_inputs_unchanged': True}, sort_keys=True))
        return 1
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
