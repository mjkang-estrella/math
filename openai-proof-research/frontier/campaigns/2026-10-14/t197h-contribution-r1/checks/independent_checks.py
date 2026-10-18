#!/usr/bin/env python3
"""MIT. Read-only identity checks made by the contribution reviewer, independent of the author's selection files.

Compares every private preprint body of the r49 packet, and every comparator body retrieved by this review,
by its own repository path against the separately anchored complete sources/preprints-tree.json.
"""
import hashlib, json, sys
from pathlib import Path

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_SHA256 = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
AUTHOR = {
    'MANIFEST.json': '819bc0a77c9ae52ca8a1b2193f64fc2f84754c17b6d5e0750c0be0ae351fd8b2',
    'verify.py': '3483b937b1a143659f6ade296c6bebd1dc177c8122e99adfbfd30c43db06f51a',
    'candidate.md': '5f02ca9695fe35564baa7f155bd541fe3cc5e5195ec0205547ca332660bc75c9',
    'original-scope.txt': '55cc403d7568ea83c45bb436d5b5084fdb82a59825ed4a945bf24ec67a2b0191',
    'checkpoint.md': 'b06cb4badb8940ccfc158d6a8f36a7c717dfb835fb85ca8aa07864bfa835e176',
}


def sha(b):
    return hashlib.sha256(b).hexdigest()


def gitblob(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()


def compare(private_root, canon):
    out = []
    for f in sorted(private_root.rglob('*')):
        if f.is_symlink() or not f.is_file():
            continue
        rel = f.relative_to(private_root).as_posix()
        if not rel.startswith('preprints/'):
            continue
        b = f.read_bytes(); g = gitblob(b)
        out.append({'path': rel, 'git_blob_sha1': g, 'sha256': sha(b), 'bytes': len(b),
                    'canonical_match': canon.get(rel) == g,
                    'url': 'https://raw.githubusercontent.com/openai/math/%s/%s' % (PIN, rel)})
    return out


def main():
    here = Path(__file__).resolve().parent.parent
    proj = here.parents[3]
    tree_raw = (proj / 'sources' / 'preprints-tree.json').read_bytes()
    assert sha(tree_raw) == TREE_SHA256, 'canonical tree anchor mismatch'
    tree = json.loads(tree_raw)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    canon = {e['path']: e['sha'] for e in tree['tree'] if e['type'] == 'blob'}
    r49 = here.parent / 'fresh-structural-discovery-r49'
    author = {k: sha((r49 / k).read_bytes()) == v for k, v in AUTHOR.items()}
    a = compare(r49 / 'private', canon)
    c = compare(here / 'private', canon)
    ok = all(author.values()) and len(a) == 29 and all(x['canonical_match'] for x in a + c)
    print(json.dumps({'status': 'PASS' if ok else 'FAIL', 'canonical_tree_sha256': TREE_SHA256,
                      'canonical_entries': len(tree['tree']), 'truncated': False,
                      'author_frozen_hashes_match': author,
                      'author_private_preprint_blobs': {'count': len(a), 'all_match': all(x['canonical_match'] for x in a)},
                      'reviewer_comparator_blobs': c,
                      'scope': 'Identity only. Upstream mathematics stipulated; no proof or novelty certified.'}, indent=2))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
