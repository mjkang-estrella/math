#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT; see ../LICENSE-MIT.
"""Read-only integrity verification. NOT a mathematical/contribution check."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

PRIOR_ANCHOR = '88428e36011c09d7920f4ebf36da39511af77f1bd770220d3f0ce49df02ee6d2'
SCOPE_SHA256 = '1b6e3b67f7a9ff756eb507a3c8f332048de2cbab0eae5e62b9fe8cd4e0a7e80a'
COMMIT = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
META = {'seal.json', 'input-manifest.json', 'output-manifest.json'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def relative(name):
    require(isinstance(name, str), 'non-string path')
    p = Path(name)
    require(not p.is_absolute() and p.as_posix() == name
            and name not in {'', '.'} and '..' not in p.parts, 'unsafe path')
    return p


def inventory(root):
    entries = list(root.rglob('*'))
    require(all(not p.is_symlink() for p in entries), 'symlink in package')
    require(all(p.is_file() or p.is_dir() for p in entries), 'nonregular entry')
    return ({p.relative_to(root).as_posix() for p in entries if p.is_file()},
            {p.relative_to(root).as_posix() for p in entries if p.is_dir()})


def package(root, anchor):
    seal_bytes = (root / 'seal.json').read_bytes()
    require(sha(seal_bytes) == anchor, 'external seal anchor mismatch')
    seal = json.loads(seal_bytes)
    expected = set(META)
    roles = {}
    for role in ('inputs', 'outputs'):
        spec = seal[role]
        require(spec['manifest'] == ('input' if role == 'inputs' else 'output')
                + '-manifest.json', 'wrong manifest name')
        data = (root / spec['manifest']).read_bytes()
        require(len(data) == spec['manifest_size'] and
                sha(data) == spec['manifest_sha256'], 'manifest authentication failed')
        manifest = json.loads(data)
        require(manifest['role'] == role, 'manifest role mismatch')
        records = manifest['files']
        require(len(records) == spec['count'] == manifest['count'], 'count mismatch')
        total = 0
        for item in records:
            name = item['path']
            path = relative(name)
            require(name not in expected, 'duplicate/metadata payload path')
            expected.add(name)
            payload = (root / path).read_bytes()
            require(len(payload) == item['size'] and sha(payload) == item['sha256'],
                    'payload mismatch: ' + name)
            total += len(payload)
        require(total == spec['total_bytes'] == manifest['total_bytes'], 'byte total mismatch')
        roles[role] = {'files': len(records), 'bytes': total}
    files, dirs = inventory(root)
    require(files == expected, 'exact file membership mismatch')
    expected_dirs = {p.as_posix() for name in expected for p in Path(name).parents
                     if p.as_posix() != '.'}
    require(dirs == expected_dirs, 'exact directory membership mismatch')
    observed = []
    for name in sorted(expected):
        payload = (root / name).read_bytes()
        observed.append({'path': name, 'size': len(payload), 'sha256': sha(payload)})
    return seal, roles, observed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seal', required=True, help='externally supplied SHA256 of seal.json')
    args = parser.parse_args()
    require(len(args.seal) == 64 and all(c in '0123456789abcdef' for c in args.seal),
            'invalid external seal')
    own = Path(__file__).resolve().parents[1]
    repo = own.parents[3]
    seal, roles, own_records = package(own, args.seal)
    require(seal['schema'] == 'ft2-r2-integrity-v1', 'wrong schema')
    require(seal['source_commit'] == COMMIT and seal['scope_sha256'] == SCOPE_SHA256,
            'wrong scope/source')
    scope = (own / 'original-scope.md').read_bytes()
    require(sha(scope) == SCOPE_SHA256, 'scope authentication failed')

    # Only this fixed, externally anchored historical tree is read outside own.
    # Never open the current campaign ledger, current AGENTS or live context.
    prior = own.parent / 'fresh-structural-discovery-r14'
    _, _, prior_records = package(prior, PRIOR_ANCHOR)
    require(len(prior_records) == 49, 'wrong historical file count')
    require(scope == (prior / 'original-scope.md').read_bytes(), 'scope bytes changed')
    historical = json.loads((own / 'inputs/r14-authentication.json').read_bytes())
    require(historical['anchor'] == PRIOR_ANCHOR and historical['exact_files']
            and historical['exact_directories'], 'wrong history authentication receipt')
    pref = prior.relative_to(repo).as_posix() + '/'
    expanded = [{**x, 'path': pref + x['path']} for x in prior_records]
    require(expanded == historical['records'] and historical['owned_files'] == 49
            and historical['owned_bytes'] == sum(x['size'] for x in prior_records),
            'historical receipt disagrees')

    tree = json.loads((prior / 'inputs/context/preprints-tree.json').read_bytes())
    require(tree['truncated'] is False and len(tree['tree']) == 13223,
            'incomplete historical catalogue')
    lookup = {x['path']: x for x in tree['tree']}
    pinned = json.loads((prior / 'inputs/pinned-records.json').read_bytes())
    require(len(pinned) == 15, 'wrong historical pinned count')
    for item in pinned:
        payload = (prior / relative(item['file'])).read_bytes()
        require(len(payload) == item['size'] and sha(payload) == item['sha256'],
                'pinned content mismatch')
        blob = hashlib.sha1(b'blob ' + str(len(payload)).encode('ascii')
                            + b'\0' + payload).hexdigest()
        require(blob == item['git_blob'], 'Git blob mismatch')
        options = [item['path'], item['path'].removeprefix('preprints/')]
        found = [lookup[name] for name in options if name in lookup]
        require(len(found) == 1 and found[0]['sha'] == blob, 'Git tree membership mismatch')

    refs = json.loads((own / 'inputs/pinned-references.json').read_bytes())
    require(refs['commit'] == COMMIT and refs['history_anchor'] == PRIOR_ANCHOR
            and len(refs['records']) == 7, 'wrong selected references')
    by_path = {x['path']: x for x in pinned}
    for item in refs['records']:
        ref = dict(item)
        location = ref.pop('history_file')
        require(ref == by_path.get(ref['path']) and location == pref + ref['file'],
                'selected reference mismatch')

    upstream = json.loads((own / 'inputs/context/upstream.json').read_bytes())
    require(upstream['commit'] == COMMIT, 'snapshot upstream mismatch')
    receipt = json.loads((own / 'inputs/unchanged-source-receipt.json').read_bytes())
    baseline = json.loads((own / 'inputs/source-baseline.json').read_bytes())
    require(receipt['future_mutable_dependency'] is False and
            baseline['live_ledger_is_not_a_verification_dependency'] is True,
            'mutable dependency forbidden')
    require(receipt['r14_records_checked_unchanged'] == 49 and
            receipt['r14_anchor'] == PRIOR_ANCHOR, 'wrong history observation')
    original = {x['path']: x for x in baseline['records']}
    require(len(original) == len(receipt['fixed_source_records']) == 5,
            'wrong fixed-source observations')
    for item in receipt['fixed_source_records']:
        before = original[item['path']]
        require(item['before_size'] == before['size'] == item['after_size'] and
                item['before_sha256'] == before['sha256'] == item['after_sha256']
                and item['unchanged_when_checked'], 'changed-source observation')
    ledger = (own / 'inputs/context/ledger.md').read_bytes()
    require(len(ledger) == receipt['ledger_start_size'] and
            sha(ledger) == receipt['ledger_start_sha256'], 'ledger snapshot mismatch')
    status = json.loads((own / 'status.json').read_bytes())
    require(status['status'] == 'UNRESOLVED_FULL_FT2_AFTER_TWO_ATTEMPTS' and
            status['accepted_count'] == 4 and status['nominated'] is False and
            status['independent_math_pass'] is False and
            status['independent_contribution_pass'] is False, 'disposition mismatch')
    print(json.dumps({'result': 'INTEGRITY_OK_ONLY', 'research_status': status['status'],
                      'owned_files': len(own_records),
                      'owned_bytes': sum(x['size'] for x in own_records),
                      'roles': roles, 'metadata_files': 3,
                      'exact_owned_files_and_directories': True,
                      'historical_files': len(prior_records),
                      'exact_historical_files_and_directories': True,
                      'pinned_git_blobs': len(pinned), 'selected_references': 7,
                      'future_live_mutable_files_read': 0, 'files_written': 0,
                      'mathematical_check_executed': False}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, TypeError) as error:
        print('INTEGRITY_REJECT: ' + str(error), file=sys.stderr)
        sys.exit(1)
