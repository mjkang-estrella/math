#!/usr/bin/env python3
"""MIT; exact inventory verification, never mathematical proof."""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def inventory(root):
    files, dirs = {}, []
    if root.is_symlink() or not root.is_dir():
        raise ValueError('root is not a regular directory')
    def visit(base):
        for p in sorted(base.iterdir()):
            st = p.lstat()
            rel = p.relative_to(root).as_posix()
            if stat.S_ISLNK(st.st_mode):
                raise ValueError('symlink: ' + rel)
            if stat.S_ISDIR(st.st_mode):
                dirs.append(rel)
                visit(p)
            elif stat.S_ISREG(st.st_mode):
                if st.st_nlink != 1:
                    raise ValueError('hardlink: ' + rel)
                if rel != 'manifest.json':
                    files[rel] = {'sha256': sha(p), 'bytes': st.st_size}
            else:
                raise ValueError('nonregular object: ' + rel)
    visit(root)
    return {'files': files, 'directories': sorted(dirs)}


def safe_name(name):
    p = PurePosixPath(name)
    return isinstance(name, str) and name != '' and not p.is_absolute() and all(x not in ('', '.', '..') for x in name.split('/')) and '\\' not in name and str(p) == name


def verify(root, anchor):
    if len(anchor) != 64 or any(c not in '0123456789abcdef' for c in anchor):
        raise ValueError('invalid external anchor')
    m = root / 'manifest.json'
    st = m.lstat()
    if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
        raise ValueError('manifest is not a single-linked regular file')
    if sha(m) != anchor:
        raise ValueError('external anchor mismatch')
    expected = json.loads(m.read_text())
    if set(expected) != {'files', 'directories'}:
        raise ValueError('manifest schema mismatch')
    if not isinstance(expected['files'], dict) or not isinstance(expected['directories'], list):
        raise ValueError('manifest inventory schema')
    names = list(expected['files']) + expected['directories']
    if len(names) != len(set(names)) or any(not safe_name(n) for n in names) or 'manifest.json' in names:
        raise ValueError('unsafe or duplicate manifest path')
    actual = inventory(root)
    if actual != expected:
        af, ef = set(actual['files']), set(expected['files'])
        ad, ed = set(actual['directories']), set(expected['directories'])
        changed = sorted(n for n in af & ef if actual['files'][n] != expected['files'][n])
        raise ValueError(json.dumps({'missing_files': sorted(ef-af), 'extra_files': sorted(af-ef), 'changed_files': changed, 'missing_dirs': sorted(ed-ad), 'extra_dirs': sorted(ad-ed)}))
    for row in json.loads((root/'identity-receipts.json').read_text()):
        for key in ['pdf', 'text']:
            if not safe_name(row[key]) or not row[key].startswith('private/'):
                raise ValueError('unsafe primary path')
            if sha(root/row[key]) != row[key+'_sha256']:
                raise ValueError('primary identity mismatch')
        import subprocess
        replay = subprocess.run(['pdftotext', '-layout', str(root/row['pdf']), '-'], capture_output=True, check=True).stdout
        if hashlib.sha256(replay).hexdigest() != row['text_sha256']:
            raise ValueError('primary text extraction mismatch')
    return {'status': 'PASS_INTEGRITY_ONLY', 'primary_pairs': len(json.loads((root/'identity-receipts.json').read_text())), 'manifest_sha256': anchor, 'files': len(actual['files']), 'directories': len(actual['directories'])}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path(__file__).absolute().parent)
    parser.add_argument('--anchor', required=True)
    args = parser.parse_args()
    try:
        print(json.dumps(verify(args.root, args.anchor), sort_keys=True))
    except (ValueError, OSError, TypeError, json.JSONDecodeError) as exc:
        print(json.dumps({'status': 'REJECT', 'reason': str(exc)}, sort_keys=True))
        raise SystemExit(1)

if __name__ == '__main__':
    main()
