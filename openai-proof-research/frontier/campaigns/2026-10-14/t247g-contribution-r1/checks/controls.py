#!/usr/bin/env python3
"""MIT. Reason-checked controls on disposable copies of a sealed packet.

The anchor is supplied by the caller, and the scratch directory must be new and
outside the packet, so the packet under test is never mutated.
"""
import argparse, hashlib, importlib.util, json, os, shutil, sys
from pathlib import Path

# Importing verify.py must not create __pycache__ inside the packet under test.
sys.dont_write_bytecode = True

REASONS = {
    'wrong_anchor': 'external manifest anchor mismatch',
    'malformed_anchor': 'external anchor must be 64 lowercase hex digits',
    'changed_review': 'payload mismatch: review.md',
    'changed_private_body': 'payload mismatch: private/primary/arxiv-2609.07996v1.layout.txt',
    'missing_payload': 'exact file inventory mismatch',
    'extra_file': 'exact file inventory mismatch',
    'extra_private_file': 'exact file inventory mismatch',
    'extra_empty_directory': 'exact directory inventory mismatch',
    'root_symlink': 'symlink or nonregular node: .',
    'payload_symlink': 'symlink or nonregular node: review.md',
    'payload_hardlink': 'hardlinked regular file: reading-limits.md',
    'fifo': 'symlink or nonregular node: fifo',
    'nested_manifest': 'nested manifest: checks/MANIFEST.json',
    'self_resealed_wrong_external_anchor': 'external manifest anchor mismatch',
    'resealed_classification_change': 'classification line changed',
    'resealed_author_anchor_change': 'author anchor record changed',
    'resealed_primary_body_change': 'primary receipt mismatch: private/primary/smoktunowicz-2008-blms-pure.pdf',
    'resealed_upstream_body_change': 'upstream receipt mismatch: private/upstream/lean-docs-247.md',
}


def reseal(d, rel, data):
    f = d / rel
    f.write_bytes(data)
    m = json.loads((d / 'MANIFEST.json').read_text())
    for e in m['files']:
        if e['path'] == rel:
            e['bytes'] = len(data)
            e['sha256'] = hashlib.sha256(data).hexdigest()
    (d / 'MANIFEST.json').write_text(json.dumps(m, indent=2) + '\n')
    return hashlib.sha256((d / 'MANIFEST.json').read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--root', type=Path, required=True)
    p.add_argument('--expected-manifest-sha256', required=True)
    p.add_argument('--scratch', type=Path, required=True)
    a = p.parse_args()
    root = a.root.absolute()
    scratch = a.scratch.absolute()
    anchor = a.expected_manifest_sha256
    assert not scratch.exists() and root not in scratch.parents and scratch != root
    spec = importlib.util.spec_from_file_location('contrib_verifier', root / 'verify.py')
    v = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(v)
    v.check(root, anchor)
    scratch.mkdir(parents=True)
    results = []

    def run(name, mutation=None, use_anchor=None, rootlink=False):
        dest = scratch / name
        shutil.copytree(root, dest, symlinks=True)
        new_anchor = mutation(dest) if mutation else None
        target = dest
        if rootlink:
            target = scratch / (name + '-link')
            target.symlink_to(dest, target_is_directory=True)
        given = use_anchor or new_anchor or anchor
        try:
            v.check(target, given)
            accepted, reason = True, 'PASS'
        except Exception as e:
            accepted, reason = False, str(e)
        expected = name == 'positive_copy'
        assert accepted == expected, (name, accepted, reason)
        if not expected:
            assert reason.startswith(REASONS[name]), (name, reason)
        results.append({'case': name, 'expected': 'accept' if expected else 'reject',
                        'anchor': 'mutated-manifest' if new_anchor else ('caller' if not use_anchor else 'override'),
                        'actual': reason})

    def append(rel):
        return lambda d: (d / rel).write_bytes((d / rel).read_bytes() + b'changed\n') and None

    def hardlink(d):
        (d / 'review.md').unlink()
        os.link(d / 'reading-limits.md', d / 'review.md')

    def symlink(d):
        (d / 'review.md').unlink()
        (d / 'review.md').symlink_to('reading-limits.md')

    def self_reseal(d):
        reseal(d, 'review.md', (d / 'review.md').read_bytes() + b'changed\n')
        return None

    def class_change(d):
        t = (d / 'review.md').read_text(encoding='utf-8').replace(
            '**Classification: TECHNICAL.**', '**Classification: SUBSTANTIAL.**', 1)
        return reseal(d, 'review.md', t.encode('utf-8'))

    def author_anchor_change(d):
        t = (d / 'input-authentication.json').read_text(encoding='utf-8').replace(
            '"author_external_anchor_used": "38b7', '"author_external_anchor_used": "0000', 1)
        return reseal(d, 'input-authentication.json', t.encode('utf-8'))

    try:
        run('positive_copy')
        run('wrong_anchor', use_anchor='0' * 64)
        run('malformed_anchor', use_anchor='not-a-hash')
        run('changed_review', append('review.md'))
        run('changed_private_body', append('private/primary/arxiv-2609.07996v1.layout.txt'))
        run('missing_payload', lambda d: (d / 'reading-limits.md').unlink())
        run('extra_file', lambda d: (d / 'extra.txt').write_text('extra') and None)
        run('extra_private_file', lambda d: (d / 'private' / 'extra.pdf').write_text('extra') and None)
        run('extra_empty_directory', lambda d: (d / 'extra-empty').mkdir())
        run('root_symlink', rootlink=True)
        run('payload_symlink', symlink)
        run('payload_hardlink', hardlink)
        run('fifo', lambda d: os.mkfifo(d / 'fifo'))
        run('nested_manifest', lambda d: (d / 'checks' / 'MANIFEST.json').write_text('{}') and None)
        run('self_resealed_wrong_external_anchor', self_reseal)
        run('resealed_classification_change', class_change)
        run('resealed_author_anchor_change', author_anchor_change)
        run('resealed_primary_body_change', lambda d: reseal(
            d, 'private/primary/smoktunowicz-2008-blms-pure.pdf',
            (d / 'private/primary/smoktunowicz-2008-blms-pure.pdf').read_bytes() + b'%changed\n'))
        run('resealed_upstream_body_change', lambda d: reseal(
            d, 'private/upstream/lean-docs-247.md',
            (d / 'private/upstream/lean-docs-247.md').read_bytes() + b'changed\n'))
    finally:
        shutil.rmtree(scratch)
    return {'status': 'PASS', 'controls': results,
            'scope': 'Inventory/identity controls on disposable copies; no mathematical or contribution claim.'}


if __name__ == '__main__':
    print(json.dumps(main(), indent=2))
