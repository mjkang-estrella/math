#!/usr/bin/env python3
"""T296O contribution review r1: read-only identity verifier.

Integrity only. It checks bytes and exact membership of this review directory
and of the frozen author packet; it does not check any proof, contribution
verdict or acceptance.

Usage:
  python3 -B verify.py --anchor <SHA256 of this manifest.json> \
      --tree /abs/path/to/sources/preprints-tree.json [--run-controls]

Adapted from frontier/campaigns/2026-10-14/t133e-contribution-r1/verify.py
(sha256 f9c38f02...f8d2), which in turn reimplemented the author r75 checks.
Author code is not executed. Control transcripts written after sealing are
exempt by exact name only.
"""
import argparse, hashlib, json, os, shutil, stat, sys, tempfile
from pathlib import Path, PurePosixPath

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
AUTHOR_DIR = 'fresh-structural-discovery-r77'
AUTHOR_ANCHORS = {
    'MANIFEST.json': 'c8d45ad7426c78529c513258e28f4e5ade79b8b6b3c4795575d01647d3d569c5',
    'candidate.md': 'da41f84da4934967b185ce33551dabf8b4c02ab76b711f5103fe40cded4ac857',
    'comparison.md': 'fe6bfb5ca0962589cb9150ef82449ea0f5ddb144e9b05e5b6204b97399f058f6',
    'reading-limits.md': '86522bd021c1c20f9e3a61cfb970b3a469fec9ea2370721e70dc4d46ba70fc50',
    'scope-freeze.md': '66056cf6b75951e864e69b51386d9729389f3b96f67e62b6cf5064eff9101a5b',
}
TREE_SHA = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
TREE_ENTRIES = 13223
FAMILY = 'Relative-generation-and-the-generator-problem-for-finite-factors-'
N_CANONICAL = 9
EXEMPT = frozenset({'controls/controls-transcript.json'})
SCHEMA = 't296o-contribution-r1-v1'


class Fail(Exception):
    pass


def need(ok, why):
    if not ok:
        raise Fail(why)


def H(b):
    return hashlib.sha256(b).hexdigest()


def safe(name):
    p = PurePosixPath(name)
    need(isinstance(name, str) and name not in ('', '.') and str(p) == name
         and not p.is_absolute() and '..' not in p.parts, 'UNSAFE_PATH:' + repr(name))


def walk(base):
    """Exact inventory; rejects links, hardlinks and nonregular entries."""
    files, dirs = {}, set()
    st = base.lstat()
    need(stat.S_ISDIR(st.st_mode) and not stat.S_ISLNK(st.st_mode), 'ROOT_NOT_DIR')
    for dp, dn, fn in os.walk(base, followlinks=False):
        for n in dn + fn:
            p = Path(dp) / n
            rel = p.relative_to(base).as_posix()
            st = p.lstat()
            need(not stat.S_ISLNK(st.st_mode), 'SYMLINK:' + rel)
            if stat.S_ISDIR(st.st_mode):
                dirs.add(rel)
            elif stat.S_ISREG(st.st_mode):
                need(st.st_nlink == 1, 'HARDLINK:' + rel)
                files[rel] = p
            else:
                need(False, 'NONREGULAR:' + rel)
    return files, dirs


def check_review(root, anchor):
    raw = (root / 'manifest.json').read_bytes()
    need(H(raw) == anchor, 'REVIEW_ANCHOR')
    m = json.loads(raw)
    need(set(m) == {'schema', 'pin', 'verdict', 'author_anchors', 'tree_sha256',
                    'exempt', 'files', 'directories'}, 'REVIEW_SCHEMA')
    need(m['schema'] == SCHEMA and m['pin'] == PIN and m['tree_sha256'] == TREE_SHA, 'REVIEW_SCHEMA')
    need(m['author_anchors'] == AUTHOR_ANCHORS, 'REVIEW_AUTHOR_ANCHORS')
    need(sorted(m['exempt']) == sorted(EXEMPT), 'REVIEW_EXEMPT')
    for n in list(m['files']) + list(m['directories']):
        safe(n)
    files, dirs = walk(root)
    sealed = {n for n in files if n != 'manifest.json' and n not in EXEMPT}
    need(sealed == set(m['files']), 'REVIEW_MEMBERSHIP')
    need(dirs == set(m['directories']), 'REVIEW_DIRECTORIES')
    for n, v in m['files'].items():
        b = files[n].read_bytes()
        need(len(b) == v['bytes'] and H(b) == v['sha256'], 'REVIEW_PAYLOAD:' + n)
    binding = json.loads((root / 'input-binding.json').read_text())
    need(binding['author_anchors'] == m['author_anchors'] and binding['pin'] == PIN, 'REVIEW_BINDING')
    return len(sealed), len(dirs)


def check_author(author, tree_path):
    files, dirs = walk(author)
    raw = (author / 'MANIFEST.json').read_bytes()
    need(H(raw) == AUTHOR_ANCHORS['MANIFEST.json'], 'AUTHOR_ANCHOR')
    d = json.loads(raw)
    for n in d:
        safe(n)
    need(set(d) == set(files) - {'MANIFEST.json'}, 'AUTHOR_MEMBERSHIP')
    want_dirs = set()
    for n in d:
        want_dirs.update(str(q) for q in PurePosixPath(n).parents if str(q) != '.')
    need(want_dirs == dirs, 'AUTHOR_DIRECTORIES')
    for n, v in d.items():
        b = files[n].read_bytes()
        need(len(b) == v['bytes'] and H(b) == v['sha256'], 'AUTHOR_PAYLOAD:' + n)
    for n, h in AUTHOR_ANCHORS.items():
        need(H(files[n].read_bytes()) == h, 'AUTHOR_FILE_ANCHOR:' + n)
    tb = tree_path.read_bytes()
    need(H(tb) == TREE_SHA, 'TREE_ANCHOR')
    t = json.loads(tb)
    need(len(t['tree']) == TREE_ENTRIES and t.get('truncated') is False, 'TREE_COMPLETE')
    es = {e['path']: e for e in t['tree']}
    s = json.loads(files['source-receipts.json'].read_text())
    need(s['pin'] == PIN and s['tree_sha256'] == TREE_SHA, 'RECEIPT_PIN')
    selected = {e['path'] for e in t['tree'] if e['type'] == 'blob' and FAMILY in e['path']
                and not e['path'].endswith('.pdf')}
    need(len(selected) == N_CANONICAL == len(s['files'])
         and {v['source_path'] for v in s['files']} == selected, 'CANONICAL_SELECTION')
    for v in s['files']:
        safe(v['path'])
        need(v['path'] == 'private/canonical/' + v['source_path'], 'CANONICAL_PATH:' + v['path'])
        need(v['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + v['source_path'],
             'SOURCE_URL:' + v['path'])
        b = files[v['path']].read_bytes()
        g = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        need(g == v['git_blob'] == es[v['source_path']]['sha'] and H(b) == v['sha256']
             and len(b) == v['bytes'], 'CANONICAL_BLOB:' + v['source_path'])
    pr = json.loads(files['primary-receipts.json'].read_text())
    need(len(pr) == 3, 'PRIMARY_COUNT')
    for v in pr:
        safe(v['file']); safe(v['text_file'])
        need(H(files[v['file']].read_bytes()) == v['sha256']
             and H(files[v['text_file']].read_bytes()) == v['text_sha256'], 'PRIMARY_RECEIPT:' + v['file'])
    return len(d), len(dirs)


def run(root, anchor, tree):
    rf, rd = check_review(root, anchor)
    af, ad = check_author(root.parent / AUTHOR_DIR, tree)
    return {'status': 'PASS_INTEGRITY_ONLY', 'review_files_sealed': rf, 'review_directories': rd,
            'author_payloads': af, 'author_directories': ad, 'canonical_blobs': N_CANONICAL,
            'tree_entries': TREE_ENTRIES, 'verdict_recorded': 'TECHNICAL (not checked by this script)'}


def controls(root, anchor, tree):
    """Copy both directories and the tree to a temporary place; mutate copies only."""
    review_name = root.name
    cases = []

    def case(name, expect, mutate):
        tmp = Path(tempfile.mkdtemp(prefix='t296o-contrib-ctl-'))
        try:
            shutil.copytree(root, tmp / review_name, symlinks=True)
            shutil.copytree(root.parent / AUTHOR_DIR, tmp / AUTHOR_DIR, symlinks=True)
            shutil.copyfile(tree, tmp / 'preprints-tree.json')
            r, a, t = tmp / review_name, tmp / AUTHOR_DIR, tmp / 'preprints-tree.json'
            ret = mutate(r, a, t)
            use_anchor = ret if isinstance(ret, str) else anchor
            try:
                out = run(r, use_anchor, t)['status']
            except Fail as e:
                out = str(e)
            # A hardlinked pair may be reported under either name, so match the prefix.
            ok = out == expect or (expect.endswith(':') and out.startswith(expect))
            cases.append({'case': name, 'expected': expect, 'observed': out, 'ok': ok})
        finally:
            shutil.rmtree(tmp)

    def append(p):
        with open(p, 'ab') as f:
            f.write(b'\n')

    blob = ('private/canonical/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-'
            'September-23-2026/build/sections/perturbation.tex')
    case('positive-copy', 'PASS_INTEGRITY_ONLY', lambda r, a, t: None)
    case('wrong-review-anchor', 'REVIEW_ANCHOR', lambda r, a, t: '0' * 64)
    case('changed-review-file', 'REVIEW_PAYLOAD:review.md', lambda r, a, t: append(r / 'review.md'))
    case('extra-review-file', 'REVIEW_MEMBERSHIP', lambda r, a, t: (r / 'extra.txt').write_text('x'))
    case('empty-review-directory', 'REVIEW_DIRECTORIES', lambda r, a, t: (r / 'emptydir').mkdir())
    case('review-symlink', 'SYMLINK:link', lambda r, a, t: os.symlink('review.md', r / 'link'))
    case('review-hardlink', 'HARDLINK:', lambda r, a, t: os.link(r / 'review.md', r / 'hard'))
    case('review-fifo', 'NONREGULAR:fifo', lambda r, a, t: os.mkfifo(r / 'fifo'))
    case('changed-author-candidate', 'AUTHOR_PAYLOAD:candidate.md', lambda r, a, t: append(a / 'candidate.md'))
    case('changed-author-manifest', 'AUTHOR_ANCHOR', lambda r, a, t: append(a / 'MANIFEST.json'))
    case('extra-author-file', 'AUTHOR_MEMBERSHIP', lambda r, a, t: (a / 'extra.txt').write_text('x'))
    case('author-symlink', 'SYMLINK:link', lambda r, a, t: os.symlink('candidate.md', a / 'link'))
    case('changed-canonical-blob', 'AUTHOR_PAYLOAD:' + blob, lambda r, a, t: append(a / blob))
    case('changed-primary-text', 'AUTHOR_PAYLOAD:private/primary/similarity.txt',
         lambda r, a, t: append(a / 'private/primary/similarity.txt'))
    case('changed-tree', 'TREE_ANCHOR', lambda r, a, t: append(t))
    return {'controls': cases, 'all_ok': all(c['ok'] for c in cases),
            'limits': 'Byte/membership controls on temporary copies only; not mathematics.'}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--anchor', required=True)
    ap.add_argument('--tree', type=Path, required=True)
    ap.add_argument('--run-controls', action='store_true')
    a = ap.parse_args()
    root = Path(__file__).absolute().parent
    try:
        need(len(a.anchor) == 64 and all(c in '0123456789abcdef' for c in a.anchor), 'MALFORMED_ANCHOR')
        res = run(root, a.anchor, a.tree)
        if a.run_controls:
            res['control_run'] = controls(root, a.anchor, a.tree)
            need(res['control_run']['all_ok'], 'CONTROL_MISMATCH:' + json.dumps(res['control_run']))
        print(json.dumps(res, indent=1))
    except Fail as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
