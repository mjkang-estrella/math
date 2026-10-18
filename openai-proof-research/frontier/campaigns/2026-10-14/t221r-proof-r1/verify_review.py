#!/usr/bin/env python3
"""MIT. T221R proof review r1: sealed-packet verifier and copied controls.

Integrity, source identity and finite replays only. Nothing here proves
mathematics; the review verdict rests on review.md's arguments.
"""
import argparse
import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
from pathlib import Path, PurePosixPath

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
AUTHOR_REL = 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r44'
AUTHOR_ANCHOR = 'c288940c8c88f67a7374d998a7c49d822f64000abb981517303f1bf4af9739c6'
AUTHOR_PINS = {
    'verify.py': '22bc163b277aa160698b01a7d3a4104e3025c7a17cdd51274ddbbb59f2c38b82',
    'proof.md': 'c2d6631489bc3e2c31dfd2eb986a1987ff477b55c3a837556e3a0923a67fefa0',
    'original-scope.txt': '26312b8fd6fb6a4bacb27085f0b46b760cc8f884754bed03e937c1b40328693c',
    'reading-and-comparison.md': '11d63dd5cfbf1a6b63a0fdbcadc7dda31a4f0c933c0ea3462d4843678ddebc1d',
}
CANON_TREE_SHA = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
FAMILY = 'preprints/The-Mezard-Parisi-formula-for-diluted-spin-glasses-September-23-2026'
OWN_PAYLOADS = {'review.md', 'independent-checks.py', 'independent-checks-output.json',
                'verify_review.py'}


class Reject(Exception):
    pass


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def git_blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def no_symlink_path(p):
    p = Path(os.path.abspath(p))
    for a in [p] + list(p.parents):
        if a.is_symlink():
            raise Reject('symlink in root or ancestor: ' + str(a))
    if not p.is_dir():
        raise Reject('not a directory: ' + str(p))
    return p


def safe_name(name):
    p = PurePosixPath(name)
    return (isinstance(name, str) and name != '' and not p.is_absolute()
            and all(x not in ('', '.', '..') for x in name.split('/'))
            and '\\' not in name and str(p) == name)


def inventory(root):
    files, dirs = {}, []

    def visit(base):
        for p in sorted(base.iterdir()):
            st = p.lstat()
            rel = p.relative_to(root).as_posix()
            if stat.S_ISLNK(st.st_mode):
                raise Reject('payload symlink: ' + rel)
            if stat.S_ISDIR(st.st_mode):
                dirs.append(rel)
                visit(p)
            elif stat.S_ISREG(st.st_mode):
                if st.st_nlink != 1:
                    raise Reject('hardlink: ' + rel)
                if rel != 'manifest.json':
                    files[rel] = {'sha256': sha(p), 'bytes': st.st_size}
            else:
                raise Reject('nonregular node: ' + rel)
    visit(root)
    return {'files': files, 'directories': sorted(dirs)}


def check_sealed(root, anchor, label):
    if len(anchor) != 64 or any(c not in '0123456789abcdef' for c in anchor):
        raise Reject(label + ': invalid external anchor')
    root = no_symlink_path(root)
    m = root / 'manifest.json'
    st = m.lstat()
    if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
        raise Reject(label + ': manifest not a single-linked regular file')
    raw = m.read_bytes()
    if hashlib.sha256(raw).hexdigest() != anchor:
        raise Reject(label + ': external anchor mismatch')
    expected = json.loads(raw)
    if not isinstance(expected, dict) or set(expected) != {'files', 'directories'}:
        raise Reject(label + ': manifest schema')
    if not isinstance(expected['files'], dict) or not isinstance(expected['directories'], list):
        raise Reject(label + ': manifest inventory schema')
    names = list(expected['files']) + expected['directories']
    if len(names) != len(set(names)) or any(not safe_name(n) for n in names) \
            or 'manifest.json' in names:
        raise Reject(label + ': unsafe or duplicate manifest path')
    actual = inventory(root)
    if actual != expected:
        af, ef = set(actual['files']), set(expected['files'])
        raise Reject(label + ': inventory mismatch ' + json.dumps({
            'missing': sorted(ef - af), 'extra': sorted(af - ef),
            'changed': sorted(n for n in af & ef if actual['files'][n] != expected['files'][n]),
            'dirs_missing': sorted(set(expected['directories']) - set(actual['directories'])),
            'dirs_extra': sorted(set(actual['directories']) - set(expected['directories']))}))
    return root, actual


def canonical_checks(repo, author_root):
    repo = no_symlink_path(repo)
    author_root = no_symlink_path(author_root)
    tree_path = repo / 'sources/preprints-tree.json'
    if sha(tree_path) != CANON_TREE_SHA:
        raise Reject('canonical preprints tree hash mismatch')
    tree = json.loads(tree_path.read_text())
    if tree.get('truncated') is not False:
        raise Reject('canonical tree truncated')
    if json.loads((repo / 'sources/upstream.json').read_text())['commit'] != PIN:
        raise Reject('canonical upstream pin mismatch')
    blobs = {x['path']: x['sha'] for x in tree['tree'] if x['type'] == 'blob'}
    receipts = []
    for name in ['source-receipts.json', 'source-221-receipts.json']:
        receipts += json.loads((author_root / name).read_text())
    seen = set()
    for row in receipts:
        path = row['path']
        if not safe_name(path) or not path.startswith('preprints/') or path in seen:
            raise Reject('unsafe or duplicate receipt path')
        seen.add(path)
        data = (author_root / 'private' / path).read_bytes()
        if path not in blobs or git_blob(data) != blobs[path]:
            raise Reject('canonical Git blob mismatch: ' + path)
    family = {p for p in blobs if p.startswith(FAMILY + '/')}
    nonpdf = {p for p in family if not p.endswith('.pdf')}
    trees = {x['path'] for x in tree['tree'] if x['type'] == 'tree'
             and (x['path'] == FAMILY or x['path'].startswith(FAMILY + '/'))}
    if len(nonpdf) != 16 or len(family - nonpdf) != 1 or len(trees) != 3:
        raise Reject('family-221 canonical inventory changed')
    if not nonpdf <= seen:
        raise Reject('family-221 non-PDF blob missing: ' + json.dumps(sorted(nonpdf - seen)))
    copied_tree = (author_root / 'private/context/preprints-tree.json').read_bytes()
    copied_up = (author_root / 'private/context/upstream.json').read_bytes()
    if copied_tree != tree_path.read_bytes() or copied_up != (repo / 'sources/upstream.json').read_bytes():
        raise Reject('copied context differs from canonical')
    return {'pinned_blobs_vs_canonical': len(receipts), 'family221_nonpdf': len(nonpdf),
            'family221_pdf_not_acquired': len(family - nonpdf), 'family221_trees': len(trees)}


def run_author(root, anchor):
    return subprocess.run([sys.executable, '-B', str(root / 'verify.py'), '--root', str(root),
                           '--anchor', anchor], capture_output=True, text=True)


def author_checks(repo):
    author = no_symlink_path(Path(repo) / AUTHOR_REL)
    if sha(author / 'manifest.json') != AUTHOR_ANCHOR:
        raise Reject('author manifest anchor mismatch')
    for name, h in AUTHOR_PINS.items():
        if sha(author / name) != h:
            raise Reject('author pinned file changed: ' + name)
    _, inv = check_sealed(author, AUTHOR_ANCHOR, 'author')
    canon = canonical_checks(repo, author)
    pos = run_author(author, AUTHOR_ANCHOR)
    out = json.loads(pos.stdout) if pos.returncode == 0 else None
    if not out or out != {'status': 'PASS_INTEGRITY_ONLY', 'pinned_blobs': 26, 'primary_pairs': 6,
                          'manifest_sha256': AUTHOR_ANCHOR, 'files': 62, 'directories': 10}:
        raise Reject('author positive verification failed: ' + pos.stdout + pos.stderr)
    for wrong in ['0' * 64, AUTHOR_ANCHOR[:-1] + ('0' if AUTHOR_ANCHOR[-1] != '0' else '1')]:
        if run_author(author, wrong).returncode == 0:
            raise Reject('author wrong anchor accepted')
    return dict(canon, author_files=len(inv['files']), author_directories=len(inv['directories']))


def replay(root):
    out = subprocess.run([sys.executable, '-B', str(root / 'independent-checks.py')],
                         capture_output=True, check=True).stdout
    if out != (root / 'independent-checks-output.json').read_bytes():
        raise Reject('independent check replay mismatch')
    return True


def verify(root, repo, anchor):
    root, inv = check_sealed(root, anchor, 'review')
    if set(inv['files']) != OWN_PAYLOADS or inv['directories']:
        raise Reject('review payload set changed')
    author = author_checks(repo)
    replay(root)
    return {'status': 'PASS_REVIEW_INTEGRITY_ONLY', 'manifest_sha256': anchor,
            'review_files': len(inv['files']), 'review_directories': len(inv['directories']),
            **author, 'finite_replay': True}


def write_manifest(root):
    inv = inventory(root)
    data = (json.dumps(inv, indent=2, sort_keys=True) + '\n').encode()
    (root / 'manifest.json').write_bytes(data)
    return hashlib.sha256(data).hexdigest()


def controls(root, repo, anchor, tmpbase):
    checks = {}
    script = 'verify_review.py'

    def own(p, a, r=None):
        return subprocess.run([sys.executable, '-B', str(p / script), '--root', str(r or p),
                               '--repo', str(repo), '--anchor', a, '--no-controls'],
                              capture_output=True, text=True).returncode

    tmpbase = Path(os.path.abspath(tmpbase))
    if tmpbase == repo or repo in tmpbase.parents:
        raise Reject('control temp directory must lie outside the repository')
    with tempfile.TemporaryDirectory(prefix='t221r-review-controls-', dir=tmpbase) as td:
        real = Path(td) / 'real'
        real.mkdir()
        man = json.loads((root / 'manifest.json').read_text())

        def copy_own(name):
            p = real / name
            p.mkdir()
            for d in man['directories']:
                (p / d).mkdir(parents=True, exist_ok=True)
            for f in list(man['files']) + ['manifest.json']:
                shutil.copyfile(root / f, p / f)
            return p

        p = copy_own('own-positive')
        checks['own_copied_positive'] = own(p, anchor) == 0
        checks['own_wrong_anchor_rejected'] = own(p, '0' * 64) != 0
        link = Path(td) / 'own-root-link'
        link.symlink_to(p, target_is_directory=True)
        checks['own_root_symlink_rejected'] = own(p, anchor, link) != 0
        anc = Path(td) / 'ancestor-link'
        anc.symlink_to(real, target_is_directory=True)
        checks['own_ancestor_symlink_rejected'] = own(p, anchor, anc / 'own-positive') != 0
        mutations = {
            'changed_payload': lambda q: (q / 'review.md').write_text((q / 'review.md').read_text() + 'X\n'),
            'missing_payload': lambda q: (q / 'independent-checks-output.json').unlink(),
            'extra_payload': lambda q: (q / 'extra.txt').write_text('extra'),
            'extra_directory': lambda q: (q / 'extra-dir').mkdir(),
            'nested_manifest_name': lambda q: ((q / 'sub').mkdir(), (q / 'sub/manifest.json').write_text('{}')),
            'payload_symlink': lambda q: (q / 'link.md').symlink_to('review.md'),
            'hardlink': lambda q: os.link(q / 'review.md', q / 'hard.md'),
            'nonregular_fifo': lambda q: os.mkfifo(q / 'fifo'),
        }
        for name, mut in mutations.items():
            q = copy_own('own-' + name)
            mut(q)
            checks['own_' + name + '_rejected'] = own(q, anchor) != 0
        q = copy_own('own-output-resealed')
        (q / 'independent-checks-output.json').write_text('{}\n')
        checks['own_output_mutation_resealed_rejected_by_replay'] = own(q, write_manifest(q)) != 0

        author = Path(repo) / AUTHOR_REL
        amain = json.loads((author / 'manifest.json').read_text())

        def copy_author(name):
            p = real / name
            p.mkdir()
            for d in amain['directories']:
                (p / d).mkdir(parents=True, exist_ok=True)
            for f in list(amain['files']) + ['manifest.json']:
                shutil.copyfile(author / f, p / f)
            return p

        src = FAMILY + '/build/sections/perturbations.tex'
        a = copy_author('author-positive')
        checks['author_copied_positive'] = run_author(a, AUTHOR_ANCHOR).returncode == 0
        checks['author_copied_wrong_anchor_rejected'] = run_author(a, '0' * 64).returncode != 0

        def expect_reason(q, new_anchor, reason):
            r = run_author(q, new_anchor)
            return r.returncode != 0 and reason in r.stdout

        q = copy_author('author-proof-changed')
        (q / 'proof.md').write_text((q / 'proof.md').read_text() + 'X\n')
        checks['author_proof_mutation_rejected'] = expect_reason(q, AUTHOR_ANCHOR, 'changed_files')
        q = copy_author('author-source-resealed')
        with open(q / 'private' / src, 'a') as fh:
            fh.write('% mutated\n')
        checks['author_real_source_mutation_resealed_rejected'] = expect_reason(
            q, write_manifest(q), 'source Git identity mismatch')
        q = copy_author('author-primary-resealed')
        with open(q / 'private/primary/lo2018.txt', 'a') as fh:
            fh.write('mutated\n')
        checks['author_real_primary_text_mutation_resealed_rejected'] = expect_reason(
            q, write_manifest(q), 'primary identity mismatch')
        q = copy_author('author-diagnostic-resealed')
        (q / 'diagnostic-output.json').write_text('{}\n')
        checks['author_diagnostic_output_mutation_resealed_rejected'] = expect_reason(
            q, write_manifest(q), 'diagnostic replay mismatch')
        q = copy_author('author-counterfeit')
        body = q / 'private' / src
        with open(body, 'a') as fh:
            fh.write('% counterfeit\n')
        data = body.read_bytes()
        rows = json.loads((q / 'source-221-receipts.json').read_text())
        for row in rows:
            if row['path'] == src:
                row['git_sha'] = git_blob(data)
                row['sha256'] = hashlib.sha256(data).hexdigest()
                row['bytes'] = len(data)
        (q / 'source-221-receipts.json').write_text(json.dumps(rows, indent=2) + '\n')
        ctree = json.loads((q / 'private/context/preprints-tree.json').read_text())
        for x in ctree['tree']:
            if x['path'] == src:
                x['sha'] = git_blob(data)
        (q / 'private/context/preprints-tree.json').write_text(json.dumps(ctree))
        fake = write_manifest(q)
        checks['author_consistent_counterfeit_accepted_by_author_verifier_LIMITATION'] = \
            run_author(q, fake).returncode == 0
        try:
            canonical_checks(repo, q)
            checks['author_consistent_counterfeit_rejected_by_canonical_check'] = False
        except Reject:
            checks['author_consistent_counterfeit_rejected_by_canonical_check'] = True
        anc2 = Path(td) / 'author-ancestor-link'
        anc2.symlink_to(real, target_is_directory=True)
        checks['author_ancestor_symlink_accepted_by_author_verifier_LIMITATION'] = \
            run_author(anc2 / 'author-positive', AUTHOR_ANCHOR).returncode == 0
        try:
            no_symlink_path(anc2 / 'author-positive')
            checks['author_ancestor_symlink_rejected_by_review_check'] = False
        except Reject:
            checks['author_ancestor_symlink_rejected_by_review_check'] = True
    return checks


def main():
    ap = argparse.ArgumentParser()
    here = Path(os.path.abspath(__file__)).parent
    ap.add_argument('--root', type=Path, default=here)
    ap.add_argument('--repo', type=Path, default=None)
    ap.add_argument('--anchor', required=True)
    ap.add_argument('--no-controls', action='store_true')
    ap.add_argument('--tmp', type=Path, default=Path('/var/tmp'),
                    help='base for copied controls; must be outside the repository')
    a = ap.parse_args()
    root = Path(os.path.abspath(a.root))
    repo = Path(os.path.abspath(a.repo)) if a.repo else root.parents[3]
    try:
        result = verify(root, repo, a.anchor)
        if not a.no_controls:
            c = controls(root, repo, a.anchor, a.tmp)
            result['controls'] = c
            if not all(c.values()):
                raise Reject('control failure: ' + json.dumps(c, sort_keys=True))
            after = verify(root, repo, a.anchor)
            result['original_after_controls'] = after['status']
        print(json.dumps(result, sort_keys=True))
    except (Reject, ValueError, OSError, KeyError, TypeError, json.JSONDecodeError,
            subprocess.CalledProcessError) as exc:
        print(json.dumps({'status': 'REJECT', 'reason': str(exc)}, sort_keys=True))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
