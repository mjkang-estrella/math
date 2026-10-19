#!/usr/bin/env python3
"""Read-only byte/provenance verification; caller must provide a detached anchor.

No network, writes, subprocesses or execution of any packet check code. This does
not verify mathematics, originality, contribution eligibility, or acceptance.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
AUTHOR = 'frontier/campaigns/2026-10-14/fresh-structural-discovery-r109'
AUTHOR_ANCHOR = '231ee8b0520af882eeb1c2fa1c680ff2fa32f3999345778223f7eb97a5edc5f5'
FIXED = {
    'public/scope.md': 'f3f0d5ff3faa18f6703d66ebba56a7b8cd863639b5a330d6ca595ef6ccb3af7a',
    'public/proof.md': '78d6af06489feb70090a0f752a26170d21e5381dab85d5c695b19bd0f203327e',
    'public/comparison.md': '87c725b8e620d9119bee7722eb0e1c0e48bd67ceb6d6ad62dc947610bb1fd96d',
    'scope-freeze.json': '1899ba7fecaaf3d798b728cd84da1c3786215f01e9bafc99e4c1d162fb6013c3',
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(test, message):
    if not test:
        raise ValueError(message)


def safe(base, relative):
    relative = Path(relative)
    require(not relative.is_absolute() and '..' not in relative.parts and
            relative != Path('.'), 'unsafe relative path')
    target = base/relative
    for item in (target, *target.parents):
        if item == base.parent:
            break
        require(not item.is_symlink(), 'symlink forbidden: '+str(item))
    return target


def verify(root, repo, expected):
    require(len(expected) == 64 and all(c in '0123456789abcdef' for c in expected),
            'invalid detached hash')
    raw = (root/'manifest.json').read_bytes()
    require(sha(raw) == expected, 'detached manifest anchor mismatch')
    m = json.loads(raw)
    require(m['revision'] == PIN and m['claim'] == 'T115E109', 'claim/pin mismatch')
    require(m['contribution_gate'] == 'TECHNICAL_CONDITIONAL_ON_CORRECTNESS',
            'contribution gate mismatch')
    require(m['correctness_gate'] is None and m['finding_number'] is None and
            m['accepted'] is False and m['count_change'] == 0 and
            all(x is None for x in m['downstream_gates'].values()), 'gate/count boundary')
    require(m['author_manifest_sha256'] == AUTHOR_ANCHOR, 'author handoff anchor mismatch')
    records = m['files']
    paths = [r['path'] for r in records]
    require(len(set(paths)) == len(paths), 'duplicate path')
    actual_files, actual_dirs = set(), set()
    for p in root.rglob('*'):
        require(not p.is_symlink(), 'symlink forbidden: '+str(p))
        if p.is_file():
            actual_files.add(p.relative_to(root).as_posix())
        elif p.is_dir():
            actual_dirs.add(p.relative_to(root).as_posix())
        else:
            raise ValueError('nonregular entry')
    require(actual_files == set(paths)|{'manifest.json'}, 'exact file membership mismatch')
    expected_dirs = {p.as_posix() for rel in actual_files for p in Path(rel).parents if p != Path('.')}
    require(actual_dirs == expected_dirs, 'exact directory membership mismatch')
    for r in records:
        data = safe(root, r['path']).read_bytes()
        require(len(data) == r['bytes'] and sha(data) == r['sha256'],
                'payload mismatch: '+r['path'])
    anchors = m['external_inputs']
    require(len({r['path'] for r in anchors}) == len(anchors), 'duplicate input anchor')
    for r in anchors:
        data = safe(repo, r['path']).read_bytes()
        require(len(data) == r['bytes'] and sha(data) == r['sha256'],
                'external input mismatch: '+r['path'])
    author = safe(repo, AUTHOR)
    require(sha((author/'manifest.json').read_bytes()) == AUTHOR_ANCHOR,
            'author detached manifest mismatch')
    before = json.loads((root/'private/author-before.json').read_text())
    observed = {p.relative_to(repo).as_posix() for p in author.rglob('*') if p.is_file()}
    require(observed == {r['path'] for r in before}, 'author membership changed')
    for relative, digest in FIXED.items():
        require(sha((author/relative).read_bytes()) == digest, 'frozen author body changed')
    require(json.loads((repo/'sources/upstream.json').read_text())['commit'] == PIN,
            'upstream pin changed')
    tree = json.loads((repo/'sources/preprints-tree.json').read_text())
    require(tree['truncated'] is False and len(tree['tree']) == 13223 and
            sum(x['type'] == 'blob' for x in tree['tree']) == 10373, 'incomplete preprint tree')
    entries = {x['path']: x for x in tree['tree']}
    receipts = json.loads((root/'source115-receipts.json').read_text())
    for r in receipts:
        data = safe(author, r['local']).read_bytes()
        blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(blob == r['git_blob'] == entries[r['path']]['sha'] and
                entries[r['path']]['type'] == 'blob', 'source Git identity mismatch')
        require(sha(data) == r['sha256'] and len(data) == r['bytes'], 'source receipt mismatch')
        require(r['url'] == 'https://raw.githubusercontent.com/openai/math/'+PIN+'/'+r['path'],
                'source URL not pinned')
    return dict(status='INTEGRITY_ONLY_VERIFIED', manifest_sha256=expected,
                review_payloads=len(records), external_inputs=len(anchors),
                author_files_unchanged=len(before), source115_blobs=len(receipts),
                complete_tree_entries=13223, mathematical_verdict=None,
                acceptance=None, finding_number=None)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expected-sha256', required=True)
    parser.add_argument('--repo-root', type=Path)
    args = parser.parse_args()
    root = Path(__file__).absolute().parent
    repo = args.repo_root.absolute() if args.repo_root else root.parents[3]
    try:
        result = verify(root, repo, args.expected_sha256)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps(dict(status='INTEGRITY_REJECTED', reason=str(error))), file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
