"""Read-only integrity check for the independent RF proof review; not a proof checker.
Myeongjin Kang, no affiliation. SPDX-License-Identifier: MIT
"""
import argparse
import hashlib
import json
from pathlib import Path


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def check_files(root, rows):
    names = set()
    for row in rows:
        name = row['path']
        p = root / name
        assert not Path(name).is_absolute() and '..' not in Path(name).parts
        assert name not in names, 'duplicate manifest member'
        names.add(name)
        assert p.is_file() and p.stat().st_size == row['bytes'], name
        assert digest(p) == row['sha256'], name
    return names


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seal', required=True, help='externally supplied SHA256 of review-manifest.json')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    repo = root.parents[3]
    manifest = root / 'review-manifest.json'
    assert digest(manifest) == args.seal, 'external review seal mismatch'
    own = check_files(root, json.loads(manifest.read_text())['files'])
    actual = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
    assert actual == own | {'review-manifest.json'}, 'review inventory mismatch'
    inputs = json.loads((root / 'inputs.json').read_text())
    check_files(repo, inputs['external_bindings'])
    author = repo / inputs['author_root']
    author_manifest = json.loads((author / 'sealed-manifest.json').read_text())
    author_members = check_files(author, author_manifest['files'])
    actual_author = {str(p.relative_to(author)) for p in author.rglob('*') if p.is_file()}
    assert actual_author == author_members | {'sealed-manifest.json'}, 'author inventory mismatch'
    assert digest(author / 'candidate.md') == author_manifest['candidate_sha256']
    assert digest(author / 'original-scope.md') == author_manifest['frozen_scope_sha256']
    tree = json.loads((repo / 'sources/preprints-tree.json').read_text())
    assert not tree.get('truncated', False), 'complete tree required'
    index = {row['path']: row.get('sha') for row in tree['tree']}
    receipts = json.loads((author / 'source-receipt.json').read_text())
    receipts += [json.loads((author / 'companion-check-receipt.json').read_text())]
    for row in receipts:
        b = (author / row['local']).read_bytes()
        git_blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        assert len(b) == row['bytes'] and hashlib.sha256(b).hexdigest() == row['sha256']
        assert git_blob == row['git_blob']
        assert index.get(row['path'], index.get(row['path'].removeprefix('preprints/'))) == git_blob
    primary_count = 0
    for row in json.loads((author / 'primary-receipt.json').read_text()):
        check_files(author, row['local_files'])
        primary_count += len(row['local_files'])
    print(json.dumps({'result': 'INTEGRITY_OK_ONLY', 'review_payloads': len(own),
                      'author_payloads': len(author_members), 'pinned_blobs': len(receipts),
                      'primary_pdf_text_members': primary_count,
                      'proof_program_run': False, 'writes': 0}))


if __name__ == '__main__':
    try:
        main()
    except (AssertionError, OSError, ValueError, KeyError) as exc:
        raise SystemExit('INTEGRITY_REJECT: ' + str(exc))
