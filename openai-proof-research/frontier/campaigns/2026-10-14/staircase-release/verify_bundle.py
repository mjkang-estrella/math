#!/usr/bin/env python3
"""Read-only bundle validation via a clean disposable extraction. Myeongjin Kang 2026; MIT."""
import argparse
from pathlib import Path
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import release_common as c


def extract_checked(contents, dest):
    manifest = c.decode(contents['BUNDLE-MANIFEST.json'])
    rows = c.rows_map(manifest['files'])
    c.require(set(contents) == set(rows) | {'BUNDLE-MANIFEST.json'}, 'ZIP inventory differs')
    for path, row in rows.items():
        c.require(c.record(path, contents[path]) == row, 'ZIP digest/length differs: ' + path)
    # All archive names and file modes were checked by archive_read, before writing.
    for path, data in sorted(contents.items()):
        target = dest.joinpath(*c.name(path).parts)
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as stream:
            stream.write(data)
    return manifest, rows


def verify_tree(root, trusted):
    manifest = c.decode(c.read(root, 'BUNDLE-MANIFEST.json'))
    c.require(manifest.get('schema') == 'staircase-publication-bundle-v1' and
              manifest.get('kind') == 'parent-integrated-local-package',
              'Not an actual parent-integrated package (preparation fixtures cannot pass)')
    c.require(manifest['trusted_parent_disposition_sha256'] == trusted,
              'Archive trust claim differs from independent parent digest')
    rows = c.rows_map(manifest['files'])
    for row in rows.values():
        c.checked(root, row)
    expected = {**c.frozen_selection(root), **c.owned_selection(root),
                **c.gate_records(root, manifest['gate_path'], trusted)}
    c.require(rows == expected, 'Bundle differs from explicit selected/gate inventories')
    actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
    c.require(actual == set(rows) | {'BUNDLE-MANIFEST.json'}, 'Unexpected extracted files')
    review = root / c.FORMAL_REVIEW / 'verify_review.py'
    process = subprocess.run([sys.executable, '-I', str(review)], cwd=root,
                             capture_output=True, text=True, timeout=60)
    c.require(process.returncode == 0, 'Frozen scoped review verification failed: ' + process.stderr)
    return {'status': 'PASS: selected bundle and actual manuscript bindings',
            'files': len(rows), 'formal_review_verifier': process.stdout.strip(),
            'fresh_lean_compilation': False, 'acceptance_awarded': False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('archive', type=Path)
    p.add_argument('--trusted-parent-sha256', required=True)
    p.add_argument('--archive-sha256', help='Optional independently received archive digest')
    a = p.parse_args()
    if a.archive_sha256:
        c.require(c.sha(a.archive.read_bytes()) == a.archive_sha256, 'Archive digest differs')
    contents = c.archive_read(a.archive)
    with tempfile.TemporaryDirectory(prefix='.verify-bundle-', dir=c.HERE) as d:
        dest = Path(d)
        extract_checked(contents, dest)
        print(c.encode(verify_tree(dest, a.trusted_parent_sha256)).decode(), end='')


if __name__ == '__main__':
    main()
