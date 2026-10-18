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
    tree = json.loads((root/'private/context/preprints-tree.json').read_text())
    if tree.get('truncated') is not False:
        raise ValueError('incomplete pinned tree')
    upstream = json.loads((root/'private/context/upstream.json').read_text())
    pin = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    if upstream['commit'] != pin:
        raise ValueError('pin mismatch')
    blobs = {x['path']: x['sha'] for x in tree['tree'] if x['type'] == 'blob'}
    pinned = 0
    for row in json.loads((root/'source-receipts.json').read_text()):
        if not safe_name(row['local']) or not row['local'].startswith('private/'):
            raise ValueError('unsafe source path')
        if row['url'] != 'https://raw.githubusercontent.com/openai/math/'+pin+'/'+row['path']:
            raise ValueError('source URL mismatch')
        data = (root/row['local']).read_bytes()
        blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if blob != row['git_blob'] or blob != blobs[row['path']]:
            raise ValueError('source Git identity mismatch')
        if hashlib.sha256(data).hexdigest() != row['sha256']:
            raise ValueError('source SHA256 mismatch')
        pinned += 1
    import subprocess
    primary_rows = [r for r in json.loads((root/'primary-receipts.json').read_text()) if 'error' not in r]
    for row in primary_rows:
        name = row['name']
        if name not in ['li-anth', 'kleinberg-tardos']:
            raise ValueError('unexpected primary name')
        pdf = root/'private'/(name+'.pdf')
        txt = pdf.with_suffix('.txt')
        if sha(pdf) != row['sha256'] or sha(txt) != row['text_sha256']:
            raise ValueError('primary identity mismatch')
        replay = subprocess.run(['pdftotext', '-layout', str(pdf), '-'], capture_output=True, check=True).stdout
        if hashlib.sha256(replay).hexdigest() != row['text_sha256']:
            raise ValueError('primary text extraction mismatch')
    return {'status': 'PASS_INTEGRITY_ONLY', 'pinned_blobs': pinned, 'primary_pairs': len(primary_rows), 'manifest_sha256': anchor, 'files': len(actual['files']), 'directories': len(actual['directories'])}


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
