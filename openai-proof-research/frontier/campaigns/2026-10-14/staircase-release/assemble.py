#!/usr/bin/env python3
"""Assemble only after the actual manuscript gate is integrated. Myeongjin Kang 2026; MIT."""
import argparse
from pathlib import Path
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import release_common as c


def build_contents(root, gate_path, trusted):
    payload = c.frozen_selection(root)
    owned = c.owned_selection(root)
    evidence = c.gate_records(root, gate_path, trusted)
    c.require(not (set(payload) & set(owned) or set(evidence) & (set(payload) | set(owned))),
              'Overlapping selections')
    rows = {**payload, **owned, **evidence}
    contents = {p: c.selected(root, p) for p in payload}
    contents.update({p: c.read(root, p) for p in owned})
    contents.update({p: c.checked(root, r) for p, r in evidence.items()})
    contents['BUNDLE-MANIFEST.json'] = c.encode({
        'schema': 'staircase-publication-bundle-v1', 'kind': 'parent-integrated-local-package',
        'gate_path': gate_path, 'trusted_parent_disposition_sha256': trusted,
        'acceptance_awarded_by_assembler': False, 'uploaded': False,
        'full_staircase_formalization': False,
        'files': [rows[p] for p in sorted(rows)]})
    return contents


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, default=c.ROOT)
    p.add_argument('--gate', required=True, help='Project-relative actual parent manuscript config')
    p.add_argument('--trusted-parent-sha256', required=True)
    p.add_argument('--output', type=Path, required=True, help='New ZIP; existing paths rejected')
    a = p.parse_args()
    contents = build_contents(a.root, a.gate, a.trusted_parent_sha256)
    c.archive_write(a.output, contents)
    print(c.encode(c.record(a.output.name, a.output.read_bytes())).decode(), end='')


if __name__ == '__main__':
    main()
