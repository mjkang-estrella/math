#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Exact file+directory inventory verification for this review directory.

Integrity only, never mathematics. Read-only on the verified root. --controls
copies the root into a fresh temporary directory and mutates only that copy.
--seal writes manifest.json and is for the reviewer's own sealing step.
"""
import argparse, hashlib, json, os, shutil, stat, sys, tempfile
from pathlib import Path, PurePosixPath

MANIFEST = 'manifest.json'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def inventory(root):
    st = root.lstat()
    if stat.S_ISLNK(st.st_mode) or not stat.S_ISDIR(st.st_mode):
        raise ValueError('root is not a regular directory')
    files, dirs = {}, []

    def visit(base):
        for p in sorted(base.iterdir()):
            s = p.lstat()
            rel = p.relative_to(root).as_posix()
            if stat.S_ISLNK(s.st_mode):
                raise ValueError('symlink: ' + rel)
            if stat.S_ISDIR(s.st_mode):
                dirs.append(rel)
                visit(p)
            elif stat.S_ISREG(s.st_mode):
                if s.st_nlink != 1:
                    raise ValueError('hardlink: ' + rel)
                if rel != MANIFEST:
                    files[rel] = {'sha256': sha(p), 'bytes': s.st_size}
            else:
                raise ValueError('nonregular object: ' + rel)
    visit(root)
    return {'files': files, 'directories': sorted(dirs)}


def safe_name(name):
    if not isinstance(name, str) or name == '' or '\\' in name:
        return False
    p = PurePosixPath(name)
    return not p.is_absolute() and str(p) == name and all(x not in ('', '.', '..') for x in name.split('/'))


def verify(root, anchor):
    if len(anchor) != 64 or any(c not in '0123456789abcdef' for c in anchor):
        raise ValueError('invalid external anchor')
    m = root / MANIFEST
    st = m.lstat()
    if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
        raise ValueError('manifest is not a single-linked regular file')
    if sha(m) != anchor:
        raise ValueError('external anchor mismatch')
    expected = json.loads(m.read_text())
    if set(expected) != {'files', 'directories'} or not isinstance(expected['files'], dict) or not isinstance(expected['directories'], list):
        raise ValueError('manifest schema mismatch')
    names = list(expected['files']) + expected['directories']
    if len(names) != len(set(names)) or any(not safe_name(n) for n in names) or MANIFEST in names:
        raise ValueError('unsafe or duplicate manifest path')
    actual = inventory(root)
    if actual != expected:
        af, ef = set(actual['files']), set(expected['files'])
        ad, ed = set(actual['directories']), set(expected['directories'])
        raise ValueError(json.dumps({
            'missing_files': sorted(ef - af), 'extra_files': sorted(af - ef),
            'changed_files': sorted(n for n in af & ef if actual['files'][n] != expected['files'][n]),
            'missing_dirs': sorted(ed - ad), 'extra_dirs': sorted(ad - ed)}))
    return {'status': 'PASS_INTEGRITY_ONLY', 'manifest_sha256': anchor,
            'files': len(actual['files']), 'directories': len(actual['directories'])}


def outcome(root, anchor):
    try:
        return verify(root, anchor)['status']
    except (ValueError, OSError, TypeError, json.JSONDecodeError) as exc:
        return 'REJECT: ' + str(exc)[:160]


def controls(root, anchor):
    results = {}
    wrong = anchor[:-1] + ('0' if anchor[-1] != '0' else '1')
    mutations = {
        'positive_copy': lambda c: None,
        'wrong_anchor_last_digit': None,
        'tamper_byte_review_md': lambda c: (c / 'review.md').write_bytes((c / 'review.md').read_bytes() + b'x'),
        'tamper_manifest': lambda c: (c / MANIFEST).write_bytes((c / MANIFEST).read_bytes() + b' '),
        'remove_file': lambda c: (c / 'findings.json').unlink(),
        'extra_file': lambda c: (c / 'extra.txt').write_text('x'),
        'extra_empty_dir': lambda c: (c / 'extra-dir').mkdir(),
        'symlink_added': lambda c: os.symlink('review.md', c / 'link.md'),
        'hardlink_added': lambda c: os.link(c / 'review.md', c / 'hard.md'),
        'fifo_added': lambda c: os.mkfifo(c / 'pipe'),
    }
    for name, mutate in mutations.items():
        tmp = Path(tempfile.mkdtemp(prefix='rcs128-r3-ctl-'))
        try:
            copy = tmp / 'copy'
            shutil.copytree(root, copy, symlinks=True)
            if mutate is None:
                results[name] = outcome(copy, wrong)
            else:
                mutate(copy)
                results[name] = outcome(copy, anchor)
        finally:
            shutil.rmtree(tmp)
    ok = results['positive_copy'] == 'PASS_INTEGRITY_ONLY' and all(v.startswith('REJECT') for k, v in results.items() if k != 'positive_copy')
    return {'controls': results, 'all_expected': ok}


def seal(root):
    inv = inventory(root)
    (root / MANIFEST).write_text(json.dumps(inv, indent=1, sort_keys=True) + '\n')
    return sha(root / MANIFEST)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, default=Path(__file__).absolute().parent)
    ap.add_argument('--anchor')
    ap.add_argument('--controls', action='store_true')
    ap.add_argument('--seal', action='store_true')
    a = ap.parse_args()
    if a.seal:
        print(seal(a.root))
        return
    if not a.anchor:
        ap.error('--anchor (external SHA256 of manifest.json) is required')
    try:
        out = verify(a.root, a.anchor)
    except (ValueError, OSError, TypeError, json.JSONDecodeError) as exc:
        print(json.dumps({'status': 'REJECT', 'reason': str(exc)}, sort_keys=True))
        sys.exit(1)
    if a.controls:
        out.update(controls(a.root, a.anchor))
        if not out['all_expected']:
            print(json.dumps(out, indent=1, sort_keys=True))
            sys.exit(2)
    print(json.dumps(out, indent=1, sort_keys=True))


if __name__ == '__main__':
    main()
