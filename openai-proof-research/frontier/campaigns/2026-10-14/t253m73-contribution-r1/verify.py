#!/usr/bin/env python3
"""MIT. Read-only review inventory and external-byte verification. Not a proof gate."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
AUTHOR = '831914c03b7c07541801e472d8c9672861ff108202f8df8ab16bc9f60bedce9c'
SCOPE = 'b4725ee50cba2e070c471a5e444da16b563c52db96d45500759b270f48e747d5'
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def ordinary(path):
    st = path.lstat()
    if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
        raise ValueError('not a regular single-link file: '+str(path))
    return path.read_bytes()


def safe(root, name):
    q = PurePosixPath(name)
    if q.is_absolute() or not q.parts or q.as_posix() != name or any(p in ('.', '..') for p in q.parts):
        raise ValueError('unsafe relative path: '+str(name))
    p = root
    for part in q.parts:
        p = p / part
        if p.is_symlink():
            raise ValueError('symlink: '+str(p))
    return p


def inventory(root):
    files, dirs = set(), set()
    for p in root.rglob('*'):
        name = p.relative_to(root).as_posix()
        st = p.lstat()
        if stat.S_ISDIR(st.st_mode):
            dirs.add(name)
        elif stat.S_ISREG(st.st_mode) and st.st_nlink == 1:
            files.add(name)
        else:
            raise ValueError('nonordinary inventory entry: '+name)
    return files, dirs


def verify(root, expected, repo_override=None):
    if not re.fullmatch('[0-9a-f]{64}', expected):
        raise ValueError('detached lowercase SHA256 required')
    raw = ordinary(root/'manifest.json')
    if sha(raw) != expected:
        raise ValueError('detached manifest anchor mismatch')
    m = json.loads(raw)
    if (m['schema'] != 't253m73-contribution-r1-v1' or m['target'] != 'T253M73'
            or m['pinned_revision'] != PIN or m['author_manifest_sha256'] != AUTHOR
            or m['frozen_scope_sha256'] != SCOPE or m['canonical_tree_sha256'] != TREE):
        raise ValueError('wrong review identity or external contract')
    if (m['conditional_contribution_verdict'] != 'TECHNICAL'
            or m['correctness_gate'] != 'NOT_PERFORMED' or m['campaign_credit'] != 0):
        raise ValueError('review gate/count semantics differ')
    records = m['files']
    wanted = {r['path'] for r in records}
    if len(wanted) != len(records) or wanted & {'manifest.json', 'manifest.sha256'}:
        raise ValueError('duplicate or self-referential file record')
    files, dirs = inventory(root)
    if files-{'manifest.json', 'manifest.sha256'} != wanted or dirs != set(m['directories']):
        raise ValueError('exact review inventory differs')
    for r in records:
        data = ordinary(safe(root, r['path']))
        if sha(data) != r['sha256'] or len(data) != r['bytes']:
            raise ValueError('review file changed: '+r['path'])
    if 'manifest.sha256' in files and ordinary(root/'manifest.sha256').decode().strip() != expected:
        raise ValueError('sidecar differs; sidecar is not a trust anchor')
    v = json.loads(ordinary(root/'verdict.json'))
    if (v['target'] != 'T253M73' or v['conditional_contribution_verdict'] != 'TECHNICAL'
            or v['correctness_gate'] != 'NOT_PERFORMED' or v['campaign_credit'] != 0
            or v['parent_assigns_all_other_gates'] is not True):
        raise ValueError('verdict semantics differ')
    evidence = json.loads(ordinary(root/'external-evidence.json'))
    if (evidence['author_manifest_sha256'] != AUTHOR or evidence['scope_sha256'] != SCOPE
            or evidence['canonical_tree_sha256'] != TREE):
        raise ValueError('external evidence anchors differ')
    repo = Path(repo_override or evidence['repo_root'])
    deps = evidence['fixed_files']
    if len({r['path'] for r in deps}) != len(deps):
        raise ValueError('duplicate external evidence path')
    for r in deps:
        data = ordinary(safe(repo, r['path']))
        if len(data) != r['bytes'] or sha(data) != r['sha256']:
            raise ValueError('external evidence changed: '+r['path'])
    author = safe(repo, evidence['author_root'])
    author_files, _ = inventory(author)
    anchored_author = {r['path'][len(evidence['author_root'])+1:]
                       for r in deps if r['path'].startswith(evidence['author_root']+'/')}
    if author_files != anchored_author or len(author_files) != evidence['author_files_observed']:
        raise ValueError('author exact file inventory changed')
    if sha(ordinary(author/'manifest.json')) != AUTHOR or sha(ordinary(author/'scope-T253M73.md')) != SCOPE:
        raise ValueError('frozen author contract changed')
    traw = ordinary(repo/'sources/preprints-tree.json')
    if sha(traw) != TREE:
        raise ValueError('canonical tree changed')
    tree = json.loads(traw)
    if tree['truncated'] is not False or len(tree['tree']) != 13223:
        raise ValueError('canonical tree is incomplete')
    blobs = {x['path']: x['sha'] for x in tree['tree'] if x['type'] == 'blob'}
    receipts = json.loads(ordinary(author/'source-receipts.json'))
    for r in receipts:
        data = ordinary(safe(author, r['local']))
        blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if (blobs.get(r['path']) != blob or blob != r['git_blob'] or sha(data) != r['sha256']
                or r['url'] != 'https://raw.githubusercontent.com/openai/math/'+PIN+'/'+r['path']):
            raise ValueError('pinned source receipt mismatch')
    primary = json.loads(ordinary(author/'primary-receipts.json'))
    for r in primary:
        p = safe(author, r['local'])
        if sha(ordinary(p)) != r['sha256'] or sha(ordinary(p.with_suffix('.txt'))) != r['text_sha256']:
            raise ValueError('primary receipt mismatch')
    return {'status': 'INTEGRITY_PASS', 'review_manifest_sha256': expected,
            'review_files': len(records), 'external_fixed_files': len(deps),
            'author_files_unchanged': len(author_files), 'canonical_source_blobs': len(receipts),
            'receipted_private_files': len(receipts)+2*len(primary),
            'correctness_gate': 'NOT_PERFORMED', 'campaign_credit': 0,
            'limits': 'Byte/inventory authentication only. Mutable parent context is observation-only.'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--expected-manifest-sha256', required=True)
    p.add_argument('--repo-root')
    args = p.parse_args()
    try:
        out = verify(Path(__file__).absolute().parent, args.expected_manifest_sha256, args.repo_root)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps({'status': 'REJECTED', 'reason': str(error)}))
        return 1
    print(json.dumps(out, indent=2))
    return 0


if __name__ == '__main__':
    sys.exit(main())
