#!/usr/bin/env python3
"""Read-only verifier: explicit detached anchors; no external input reads or writes."""
import argparse
import hashlib
import json
import os
import stat
from pathlib import Path, PurePosixPath

CONTROLS = {'MANIFEST.json', 'REPORT.md'}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def safe(name):
    assert isinstance(name, str) and name, 'empty/nonstring path'
    path = PurePosixPath(name)
    assert not path.is_absolute() and str(path) == name, 'noncanonical path'
    assert all(part not in ('', '.', '..') for part in path.parts), 'unsafe component'
    assert '\\' not in name and all(ord(c) >= 32 and ord(c) != 127 for c in name), 'unsafe character'
    return name

def inspect(root):
    assert stat.S_ISDIR(root.lstat().st_mode), 'root must be a real directory'
    files, dirs = {}, {'.': root.lstat().st_mode}
    for base, children, names in os.walk(root, followlinks=False):
        for name in children:
            p = Path(base) / name
            rel = safe(p.relative_to(root).as_posix())
            mode = p.lstat().st_mode
            assert stat.S_ISDIR(mode), 'symlink or special directory'
            dirs[rel] = mode
        for name in names:
            p = Path(base) / name
            rel = safe(p.relative_to(root).as_posix())
            st = p.lstat()
            assert stat.S_ISREG(st.st_mode) and st.st_nlink == 1, 'nonregular or hardlinked file'
            files[rel] = p
    return files, dirs

def check(root, final_sha, manifest_sha, report_sha):
    files, dirs = inspect(root)
    for name, anchor in [('FINAL.md', final_sha), ('MANIFEST.json', manifest_sha), ('REPORT.md', report_sha)]:
        assert isinstance(anchor, str) and len(anchor) == 64 and all(c in '0123456789abcdef' for c in anchor), 'invalid explicit anchor'
        assert name in files and sha(files[name].read_bytes()) == anchor, 'detached anchor mismatch: ' + name
    m = json.loads(files['MANIFEST.json'].read_bytes())
    assert m['version'] == 1
    records = m['files']
    names = [safe(x['path']) for x in records]
    assert names == sorted(set(names)), 'unsorted/duplicate payload records'
    assert not CONTROLS.intersection(names), 'control self-reference'
    assert set(files) == set(names) | CONTROLS, 'file membership mismatch'
    drecs = m['directories']
    dnames = [x['path'] for x in drecs]
    assert dnames == sorted(set(dnames)), 'unsorted/duplicate directory records'
    for name in dnames:
        if name != '.':
            safe(name)
    assert dirs == {x['path']: x['st_mode'] for x in drecs}, 'directory membership/full mode mismatch'
    for rec in records:
        q = files[rec['path']]
        b = q.read_bytes()
        assert len(b) == rec['bytes'] and sha(b) == rec['sha256'], 'payload mismatch: ' + rec['path']
        assert q.lstat().st_mode == rec['st_mode'], 'full file mode mismatch: ' + rec['path']
    assert set(m['control_modes']) == CONTROLS
    for name in CONTROLS:
        assert files[name].lstat().st_mode == m['control_modes'][name], 'control full mode mismatch'
    if m.get('review_bindings'):
        assert sha(files['private/author/STATEMENT.md'].read_bytes()) == '6f1c7eed54c4bee7b80a56494fddfb0e5e0bcd66f0e4b9acc2a2fdb6458f5127'
        assert sha(files['private/author/PROOF.md'].read_bytes()) == '839d48acac9b0f3e433aa26d04081e205b499f538b6b0fc5ee04f945cb44f6b5'
        tree = json.loads(files['private/source-tree.json'].read_bytes())
        auth = json.loads(files['private/source-authentication.json'].read_bytes())
        prefix = 'Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026'
        by = {x['path'].removeprefix('preprints/'): x for x in tree}
        assert len(by) == len(tree) == 16 and len(auth) == 12
        expected = {n[len(prefix)+1:]: x for n, x in by.items() if x['type'] == 'blob'}
        seen = set()
        for rec in auth:
            name = safe(rec['path'])
            assert name not in seen
            seen.add(name)
            b = files['private/source/' + name].read_bytes()
            blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
            entry = expected[name]
            assert len(b) == rec['bytes'] == entry['size']
            assert blob == rec['git_blob'] == entry['sha'] and sha(b) == rec['sha256']
            assert entry['mode'] == rec['git_mode'] == '100644'
        assert seen == set(expected)
        assert sum(x['bytes'] for x in auth if x['path'] != 'paper.pdf') == 145989
        for name, entry in by.items():
            if entry['type'] != 'tree':
                continue
            children = [(n[len(name)+1:], x) for n, x in by.items() if n.startswith(name+'/') and '/' not in n[len(name)+1:]]
            children.sort(key=lambda pair: pair[0] + ('/' if pair[1]['type'] == 'tree' else ''))
            raw = b''.join((x['mode'].lstrip('0') + ' ' + n).encode() + b'\0' + bytes.fromhex(x['sha']) for n, x in children)
            assert hashlib.sha1(b'tree ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == entry['sha']
        commit = json.loads(files['private/pinned-commit.json'].read_bytes())
        root_tree = json.loads(files['private/pinned-root-tree.json'].read_bytes())
        assert commit['sha'] == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
        assert commit['tree']['sha'] == root_tree['sha']
        assert [x['sha'] for x in root_tree['tree'] if x['path'] == 'preprints'] == ['df0564b2deaab87e07854b6344d8c2f037682e77']
    return {'payload_files': len(records), 'total_files': len(files), 'directories_including_root': len(dirs),
            'payload_bytes': sum(x['bytes'] for x in records), 'review_bindings': bool(m.get('review_bindings'))}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['root', 'final-sha', 'manifest-sha', 'report-sha']:
        parser.add_argument('--' + name, required=True)
    a = parser.parse_args()
    print('MATCH ' + json.dumps(check(Path(a.root), a.final_sha, a.manifest_sha, a.report_sha), sort_keys=True))
