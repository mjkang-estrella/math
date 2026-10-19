"""Read-only packet verifier. Integrity checks are not mathematical proof.

The expected manifest SHA256 MUST come from the detached parent handoff.
No network, subprocess, import of packet code, or filesystem mutation.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import stat
import sys

REVISION = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
SCOPE_SHA256 = '314784562d56ff8f515e81c3fc8ec4be42cceb0879650635aad07d5ee6180ed9'
OWN = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def unique_object(pairs):
    answer = {}
    for key, value in pairs:
        require(key not in answer, 'duplicate JSON key: ' + key)
        answer[key] = value
    return answer


def decode(data):
    return json.loads(data.decode('utf-8'), object_pairs_hook=unique_object)


def safe_relative(value):
    require(isinstance(value, str) and value, 'missing path')
    path = PurePosixPath(value)
    require(not path.is_absolute() and '..' not in path.parts,
            'unsafe path: ' + value)
    require(str(path) == value and '\\' not in value and '\x00' not in value,
            'noncanonical path: ' + repr(value))
    return path


def plain_file(path):
    info = path.lstat()
    require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
            'not an unlinked regular file: ' + str(path))
    return path.read_bytes()


def inventory():
    files, directories = set(), set()

    def visit(folder):
        for path in folder.iterdir():
            info = path.lstat()
            rel = path.relative_to(OWN).as_posix()
            safe_relative(rel)
            if stat.S_ISDIR(info.st_mode):
                directories.add(rel)
                visit(path)
            elif stat.S_ISREG(info.st_mode) and info.st_nlink == 1:
                files.add(rel)
            else:
                raise ValueError('link or special entry: ' + rel)

    visit(OWN)
    return files, directories


def run(expected, repository):
    require(re.fullmatch('[0-9a-f]{64}', expected) is not None,
            'expected anchor must be lowercase SHA256')
    manifest_bytes = plain_file(OWN / 'manifest.json')
    require(digest(manifest_bytes) == expected, 'detached manifest anchor mismatch')
    manifest = decode(manifest_bytes)
    require(manifest['revision'] == REVISION, 'wrong revision')
    require(manifest['scope_sha256'] == SCOPE_SHA256, 'frozen scope identity changed')
    require(manifest['status'] == 'UNRESOLVED' and manifest['count_change'] == 0,
            'packet status changed')
    records = manifest['files']
    expected_files = set()
    for record in records:
        rel = str(safe_relative(record['path']))
        require(rel != 'manifest.json' and rel not in expected_files,
                'duplicate or self-referential payload')
        expected_files.add(rel)
    actual_files, actual_directories = inventory()
    require(actual_files == expected_files | {'manifest.json'},
            'file membership mismatch')
    require(len(manifest['directories']) == len(set(manifest['directories'])),
            'duplicate directory entry')
    expected_directories = {str(safe_relative(p)) for p in manifest['directories']}
    require(actual_directories == expected_directories, 'directory membership mismatch')
    total = 0
    for record in records:
        data = plain_file(OWN / record['path'])
        require(len(data) == record['bytes'], 'size mismatch: ' + record['path'])
        require(digest(data) == record['sha256'], 'hash mismatch: ' + record['path'])
        total += len(data)
    require(digest(plain_file(OWN / 'scope.md')) == SCOPE_SHA256, 'scope mismatch')

    context = decode(plain_file(OWN / 'context-receipts.json'))
    anchors = {x['path']: x for x in context['anchors']}
    require(len(anchors) == len(context['anchors']), 'duplicate context identity')
    immutable = {'sources/upstream.json', 'sources/preprints-tree.json', 'sources/CONTENTS.md'}
    drift = []
    external_data = {}
    for rel, record in anchors.items():
        safe_relative(rel)
        try:
            data = (repository / rel).read_bytes()
        except FileNotFoundError:
            require(rel not in immutable, 'missing pinned external input: ' + rel)
            drift.append({'path': rel, 'status': 'missing'})
            continue
        unchanged = len(data) == record['bytes'] and digest(data) == record['sha256']
        if rel in immutable:
            require(unchanged, 'pinned external input changed: ' + rel)
            external_data[rel] = data
        elif not unchanged:
            drift.append({'path': rel, 'status': 'changed', 'sha256_now': digest(data)})
    require(immutable <= external_data.keys(), 'missing required external anchors')
    upstream = decode(external_data['sources/upstream.json'])
    require(upstream['commit'] == REVISION, 'external revision mismatch')
    tree = decode(external_data['sources/preprints-tree.json'])
    require(tree['truncated'] is False and len(tree['tree']) == 13223,
            'not the complete pinned tree')
    entries = {x['path']: x for x in tree['tree']}
    require(len(entries) == 13223, 'duplicate pinned tree path')
    sources = decode(plain_file(OWN / 'source-receipts.json'))
    require(len(sources) == manifest['source_receipt_count'], 'source count mismatch')
    seen = set()
    for receipt in sources:
        require(receipt['status'] == 'retrieved', 'unexpected source retrieval status')
        rel = str(safe_relative(receipt['path']))
        require(rel not in seen, 'duplicate source receipt')
        seen.add(rel)
        entry = entries[rel]
        require(entry['type'] == 'blob' and entry['sha'] == receipt['git_blob'],
                'source blob not in pinned complete tree: ' + rel)
        local = str(safe_relative(receipt['local']))
        require(local == 'private/' + rel and local in expected_files,
                'source not bound as private evidence: ' + rel)
        data = plain_file(OWN / local)
        require(len(data) == receipt['bytes'] and digest(data) == receipt['sha256'],
                'source receipt mismatch: ' + rel)
        git = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(git == receipt['git_blob'], 'source Git object mismatch: ' + rel)
        require(receipt['url'] == 'https://raw.githubusercontent.com/openai/math/'
                + REVISION + '/' + rel, 'source URL mismatch: ' + rel)
    primary = decode(plain_file(OWN / 'primary-receipts.json'))
    successes, failures = 0, 0
    for receipt in primary:
        if receipt['status'] == 'failed':
            require(bool(receipt['error']), 'failed retrieval lacks reason')
            failures += 1
            continue
        require(receipt['status'] == 'retrieved', 'unknown primary status')
        for field, hash_field in [('local', 'sha256'), ('text', 'text_sha256')]:
            rel = str(safe_relative(receipt[field]))
            require(rel.startswith('private/') and rel in expected_files,
                    'primary body not private and manifest-bound')
            require(digest(plain_file(OWN / rel)) == receipt[hash_field],
                    'primary receipt mismatch: ' + rel)
        successes += 1
    return {'integrity': 'verified', 'mathematical_status': 'UNRESOLVED',
            'count_change': 0, 'manifest_sha256': expected,
            'payload_files': len(records), 'payload_bytes': total,
            'tree_entries': len(entries), 'authenticated_source_blobs': len(seen),
            'primary_successes': successes, 'recorded_primary_failures': failures,
            'mutable_context_drift': drift,
            'limits': 'Integrity only; no mathematical proof, independent gate, or priority certification.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expected-manifest-sha256', required=True)
    parser.add_argument('--repository', type=Path, default=Path(__file__).resolve().parents[4])
    args = parser.parse_args()
    try:
        print(json.dumps(run(args.expected_manifest_sha256, args.repository), indent=2, sort_keys=True))
    except (ValueError, OSError, KeyError, TypeError) as error:
        print(json.dumps({'integrity': 'REJECTED', 'error': str(error)}), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
