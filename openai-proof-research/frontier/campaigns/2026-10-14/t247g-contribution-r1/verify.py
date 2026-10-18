#!/usr/bin/env python3
"""MIT. Read-only verification of the T247G contribution-r1 packet.

The caller MUST supply the manifest SHA256 obtained out of band; nothing in
the packet can authenticate itself.
"""
import argparse, hashlib, json, re, stat, sys
from pathlib import Path

AUTHOR_ANCHOR = '38b748ab81407bdb6bbd6b8557fc9f4d27fc094884705e8fcd9963939c4907fd'
CLASSIFICATION = '**Classification: TECHNICAL.** History eligibility: **ELIGIBLE** (bounded search).'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def git_blob(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()


def require(ok, why):
    if not ok:
        raise ValueError(why)


def safe(n):
    return (isinstance(n, str) and n not in ('', '.') and not Path(n).is_absolute()
            and '..' not in Path(n).parts and Path(n).as_posix() == n)


def scan(root):
    files, dirs = [], []

    def walk(p, rel):
        s = p.lstat()
        if stat.S_ISDIR(s.st_mode):
            dirs.append(rel)
            for q in sorted(p.iterdir(), key=lambda x: x.name):
                walk(q, q.relative_to(root).as_posix())
        elif stat.S_ISREG(s.st_mode):
            require(s.st_nlink == 1, 'hardlinked regular file: ' + rel)
            require(p.name != 'MANIFEST.json' or rel == 'MANIFEST.json', 'nested manifest: ' + rel)
            files.append(rel)
        else:
            raise ValueError('symlink or nonregular node: ' + rel)

    walk(root, '.')
    return sorted(files), sorted(dirs)


def check(root, anchor):
    require(isinstance(anchor, str) and re.fullmatch(r'[0-9a-f]{64}', anchor) is not None,
            'external anchor must be 64 lowercase hex digits')
    files, dirs = scan(root)
    require('MANIFEST.json' in files, 'missing MANIFEST.json')
    raw = (root / 'MANIFEST.json').read_bytes()
    require(sha(raw) == anchor, 'external manifest anchor mismatch')
    m = json.loads(raw)
    entries = m['files']
    names = [e['path'] for e in entries]
    require(len(names) == len(set(names)) and all(safe(n) and n != 'MANIFEST.json' for n in names),
            'invalid payload names')
    require(files == sorted(names + ['MANIFEST.json']), 'exact file inventory mismatch')
    require(dirs == m['directories'], 'exact directory inventory mismatch')
    for e in entries:
        b = (root / e['path']).read_bytes()
        require(len(b) == e['bytes'] and sha(b) == e['sha256'], 'payload mismatch: ' + e['path'])

    review = (root / 'review.md').read_text(encoding='utf-8')
    require(CLASSIFICATION in review.splitlines()[2], 'classification line changed')
    auth = json.loads((root / 'input-authentication.json').read_text(encoding='utf-8'))
    require(auth['author_external_anchor_used'] == AUTHOR_ANCHOR
            and auth['named_input_sha256_expected']['MANIFEST.json'] == AUTHOR_ANCHOR,
            'author anchor record changed')

    rr = json.loads((root / 'retrieval-receipts.json').read_text(encoding='utf-8'))
    require(len(rr['primary']) == 3 and len(rr['upstream']) == 3, 'receipt selection count mismatch')
    for e in rr['primary']:
        for k in ('pdf', 'text'):
            require(safe(e[k]) and e[k].startswith('private/') and e[k] in names,
                    'unsafe or unlisted primary path: ' + str(e[k]))
            b = (root / e[k]).read_bytes()
            require(len(b) == e[k + '_bytes'] and sha(b) == e[k + '_sha256'],
                    'primary receipt mismatch: ' + e[k])
    for e in rr['upstream']:
        require(safe(e['local']) and e['local'].startswith('private/') and e['local'] in names,
                'unsafe or unlisted upstream path')
        b = (root / e['local']).read_bytes()
        require(sha(b) == e['sha256'] and git_blob(b) == e['git_blob_sha1'] and len(b) == e['bytes'],
                'upstream receipt mismatch: ' + e['local'])
        require(e['url'].startswith('https://raw.githubusercontent.com/openai/math/'
                                    'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'), 'unpinned upstream URL')
    return {'status': 'PASS', 'payload_files': len(entries), 'directories': len(dirs),
            'primary_pdf_text_pairs': len(rr['primary']), 'upstream_files': len(rr['upstream']),
            'scope': 'Exact inventory and recorded identities only; not proof, contribution, '
                     'novelty, formal verification, or acceptance.'}


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--expected-manifest-sha256', required=True)
    p.add_argument('--root', type=Path)
    a = p.parse_args()
    root = a.root.absolute() if a.root else Path(__file__).absolute().parent
    print(json.dumps(check(root, a.expected_manifest_sha256)))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
