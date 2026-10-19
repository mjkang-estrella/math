#!/usr/bin/env python3
"""Read-only offline integrity check. Requires a detached external SHA256.

Does not execute payloads, request network access, write files, or adjudicate
mathematics. Read this program before executing it. Trust the expected digest
from the detached handoff, never solely from the neighboring seal file.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
AUTHOR = 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r107'
AUTHOR_ANCHOR = 'e3b992016df3fadbe6fc223e9f1dfb9565f435b9afe9ed81705a495453ffdb6f'
ENVELOPES = {'manifest.json', 'seal.sha256'}


def require(test, message):
    if not test:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_regular(base, name):
    require(isinstance(name, str) and name, 'invalid path')
    rel = PurePosixPath(name)
    require(not rel.is_absolute() and '..' not in rel.parts
            and rel.as_posix() == name and '\\' not in name, 'unsafe path: '+name)
    current = base
    for part in rel.parts:
        current = current / part
        require(not current.is_symlink(), 'symlink: '+name)
    require(stat.S_ISREG(current.stat().st_mode), 'not a regular file: '+name)
    return current.read_bytes()


def record_bytes(base, item):
    raw = read_regular(base, item['path'])
    require(type(item['bytes']) is int and len(raw) == item['bytes'],
            'size mismatch: '+item['path'])
    require(digest(raw) == item['sha256'], 'SHA256 mismatch: '+item['path'])
    return raw


def verify(bundle, repo, expected):
    require(re.fullmatch('[0-9a-f]{64}', expected) is not None,
            'expected digest must be 64 lowercase hex digits')
    raw = read_regular(bundle, 'manifest.json')
    require(digest(raw) == expected, 'detached external manifest mismatch')
    m = json.loads(raw)
    require(m['schema'] == 't333e107-contribution-r1-v1', 'wrong schema')
    require(m['upstream_revision'] == PIN, 'wrong upstream pin')
    require(m['verdict'] == 'TECHNICAL_CONDITIONAL_ON_CORRECTNESS'
            and m['proof_gate'] == 'NOT_DECIDED'
            and type(m['count_credit']) is int and m['count_credit'] == 0
            and m['acceptance_entered'] is False, 'status boundary changed')
    require(m['envelope_exclusions'] == sorted(ENVELOPES), 'wrong exclusions')
    require(read_regular(bundle, 'seal.sha256').decode() ==
            expected+'  manifest.json\n', 'seal copy mismatch')
    records = m['payloads']
    names = [i['path'] for i in records]
    require(len(names) == len(set(names)), 'duplicate payload path')
    require(not ENVELOPES.intersection(names), 'envelope listed as payload')
    directories = {p.as_posix() for n in names for p in PurePosixPath(n).parents
                   if p.as_posix() != '.'}
    actual = set()
    for p in bundle.rglob('*'):
        name = p.relative_to(bundle).as_posix()
        require(not p.is_symlink(), 'symlink in bundle: '+name)
        if p.is_dir():
            require(name in directories, 'unexpected directory: '+name)
        else:
            require(stat.S_ISREG(p.stat().st_mode), 'special payload: '+name)
            if name not in ENVELOPES:
                actual.add(name)
    require(actual == set(names), 'payload membership mismatch')
    for item in records:
        require(item['classification'] ==
                ('private-evidence' if item['path'].startswith('private/') else 'original'),
                'private evidence boundary mismatch')
        record_bytes(bundle, item)

    anchors = m['external_anchors']
    anchor_names = [i['path'] for i in anchors]
    require(len(anchor_names) == len(set(anchor_names)), 'duplicate external anchor')
    for item in anchors:
        record_bytes(repo, item)
    baseline = json.loads(read_regular(bundle, 'author-baseline.json'))
    require(len(baseline['files']) == 36, 'wrong author baseline count')
    for item in baseline['files']:
        require(item['path'] in anchor_names, 'unanchored author file')
        record_bytes(repo, item)
    require(digest(read_regular(repo, AUTHOR+'/manifest.json')) == AUTHOR_ANCHOR,
            'original author manifest anchor mismatch')
    for name, value in baseline['externally_supplied'].items():
        require(digest(read_regular(repo, AUTHOR+'/'+name)) == value,
                'detached author operative anchor mismatch: '+name)

    require('sources/preprints-tree.json' in anchor_names, 'complete tree unanchored')
    tree = json.loads(read_regular(repo, 'sources/preprints-tree.json'))
    require(tree['truncated'] is False and len(tree['tree']) == 13223,
            'tree must have 13223 entries and be nontruncated')
    entries = {i['path']: i for i in tree['tree']}
    require(len(entries) == 13223, 'duplicate complete-tree path')
    source = json.loads(read_regular(bundle, 'private/provenance/author-upstream.json'))
    require(source['revision'] == PIN and source['tree_entries'] == 13223
            and source['truncated'] is False, 'wrong source provenance')
    source_names = set()
    for item in source['files']:
        require(item['path'] in actual and item['path'] not in source_names,
                'missing or duplicate source payload')
        source_names.add(item['path'])
        data = record_bytes(bundle, item)
        canonical = item['upstream_path']
        require(canonical in entries and entries[canonical]['type'] == 'blob',
                'canonical source absent from complete tree')
        blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(blob == item['git_blob'] == entries[canonical]['sha'],
                'pinned Git blob mismatch: '+canonical)
        require(item['raw_url'] == 'https://raw.githubusercontent.com/openai/math/'
                +PIN+'/'+canonical, 'source URL not pinned')
    require(len(source_names) == 13, 'wrong pinned source count')
    primary = json.loads(read_regular(bundle, 'private/provenance/author-primary.json'))
    primary_names = set()
    for item in primary['files']:
        require(item['path'] in actual and item['path'] not in primary_names,
                'missing or duplicate primary payload')
        primary_names.add(item['path'])
        record_bytes(bundle, item)
        if 'derived_from' in item:
            require(item['derived_from'] in actual, 'missing derivation input')
    evidence = json.loads(read_regular(bundle, 'evidence-provenance.json'))
    for item in evidence['retained_files']:
        require(item['path'] in actual, 'unmanifested retained evidence')
        record_bytes(bundle, item)
        require(digest(read_regular(repo, item['copied_from'])) == item['sha256'],
                'retained evidence differs from anchored author bytes')
    require({i['path'] for i in evidence['retained_files']} ==
            {n for n in actual if n.startswith('private/')},
            'unaccounted private evidence')
    return {'integrity': 'verified', 'payloads': len(records),
            'external_anchors': len(anchors), 'author_files_unchanged': 36,
            'pinned_blobs': len(source_names), 'complete_tree_entries': 13223,
            'manifest_sha256': expected,
            'mathematics_or_contribution_certified': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expected-manifest', required=True)
    parser.add_argument('--repo-root', type=Path, required=True)
    parser.add_argument('--bundle-root', type=Path, default=Path(__file__).parent)
    args = parser.parse_args()
    try:
        require(not args.bundle_root.is_symlink(), 'symlink bundle root')
        result = verify(args.bundle_root.resolve(strict=True),
                        args.repo_root.resolve(strict=True), args.expected_manifest)
        print(json.dumps(result, sort_keys=True))
        return 0
    except (ValueError, KeyError, TypeError, OSError) as exc:
        print('INTEGRITY FAILURE: '+str(exc), file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
