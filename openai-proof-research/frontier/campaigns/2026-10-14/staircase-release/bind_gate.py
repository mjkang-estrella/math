#!/usr/bin/env python3
"""Make a new config from actual parent evidence; creates no verdict. Myeongjin Kang 2026; MIT."""
import argparse
from pathlib import Path
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import release_common as c


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, default=c.ROOT)
    p.add_argument('--parent-disposition', required=True)
    p.add_argument('--trusted-parent-sha256', required=True)
    p.add_argument('--artifact', action='append', default=[])
    p.add_argument('--output', required=True, help='New project-relative parent manuscript config JSON')
    a = p.parse_args()
    parent = c.record(a.parent_disposition, c.read(a.root, a.parent_disposition))
    c.require(parent['sha256'] == a.trusted_parent_sha256, 'Parent digest is not independently trusted')
    d = c.decode(c.checked(a.root, parent))
    gate = {'schema': 'staircase-release-gate-v1', 'state': 'integrated',
            'bound_paper': c.FROZEN, 'parent_disposition': parent, 'review_artifacts': []}
    for k in ['review', 'review_manifest', 'reviewer_record', 'reviewer', 'reviewer_identity_basis']:
        gate[k] = d[k]
    members = c.manifest_rows(c.checked(a.root, gate['review_manifest']), c.REVIEW)
    for path in a.artifact:
        c.require(path in members, 'Requested artifact absent from actual manifest')
        gate['review_artifacts'].append(members[path])
    # Validate fully using an in-memory config read overlay, before any write.
    c.require(a.output.startswith(c.PARENT + '/') and 'manuscript' in c.name(a.output).name and
              c.name(a.output).suffix == '.json', 'Output must be a new parent manuscript JSON')
    raw = c.encode(gate)
    original_read = c.read
    def overlay(root, path):
        return raw if path == a.output else original_read(root, path)
    c.read = overlay
    try:
        c.gate_records(a.root, a.output, a.trusted_parent_sha256)
    finally:
        c.read = original_read
    target = a.root.joinpath(*c.name(a.output).parts)
    c.require(target.parent.resolve() == target.parent.absolute() and not target.is_symlink(), 'Symlink output')
    with target.open('xb') as stream:
        stream.write(raw)
    print(c.encode(c.record(a.output, raw)).decode(), end='')


if __name__ == '__main__':
    main()
