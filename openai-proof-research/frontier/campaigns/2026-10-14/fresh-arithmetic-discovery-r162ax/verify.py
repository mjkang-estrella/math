#!/usr/bin/env python3
"""Read-only r162ax artifact authentication. No mathematical gate."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat


def sha(b):
    return hashlib.sha256(b).hexdigest()


def safe(s, directory=False):
    assert isinstance(s, str)
    if directory and s == '.':
        return s
    p = PurePosixPath(s)
    assert s and not p.is_absolute() and '\\' not in s
    assert all(t not in ('', '.', '..') for t in s.split('/'))
    assert str(p) == s
    return s


def inventory(root):
    files, dirs = {}, {'.': root.lstat().st_mode}
    assert stat.S_ISDIR(dirs['.']) and not root.is_symlink()
    for base, dn, fn in os.walk(root, followlinks=False):
        for name in dn:
            p = Path(base) / name
            s = p.relative_to(root).as_posix()
            mode = p.lstat().st_mode
            assert stat.S_ISDIR(mode) and not p.is_symlink()
            dirs[safe(s)] = mode
        for name in fn:
            p = Path(base) / name
            s = p.relative_to(root).as_posix()
            mode = p.lstat().st_mode
            assert stat.S_ISREG(mode) and not p.is_symlink()
            files[safe(s)] = mode
    return files, dirs


def unique_sorted(records, directory=False):
    keys = [safe(e['path'], directory) for e in records]
    assert keys == sorted(keys)
    assert len(keys) == len(set(keys)) == len(set(k.casefold() for k in keys))
    return dict(zip(keys, records))


def run(root, final_anchor, manifest_anchor, report_anchor):
    for value in (final_anchor, manifest_anchor, report_anchor):
        assert re.fullmatch('[0-9a-f]{64}', value)
    for name, expected in [('private/FINAL.md', final_anchor), ('MANIFEST.json', manifest_anchor), ('REPORT.md', report_anchor)]:
        p = root / name
        assert p.is_file() and not p.is_symlink()
        assert sha(p.read_bytes()) == expected, 'detached anchor: ' + name
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    assert manifest['schema'] == 'r162ax-v1'
    assert manifest['detached'] == ['MANIFEST.json', 'REPORT.md']
    files, dirs = inventory(root)
    expected_files = unique_sorted(manifest['files'])
    expected_dirs = unique_sorted(manifest['directories'], True)
    assert set(files) == set(expected_files) | set(manifest['detached']), 'file membership'
    assert set(dirs) == set(expected_dirs), 'directory membership'
    for s, e in expected_files.items():
        b = (root / s).read_bytes()
        assert len(b) == e['bytes'] and sha(b) == e['sha256'], s
        assert files[s] == e['mode'], 'file mode: ' + s
    for s, e in expected_dirs.items():
        assert dirs[s] == e['mode'], 'directory mode: ' + s
    for s in manifest['detached']:
        assert files[s] == stat.S_IFREG | 0o644, 'detached mode'

    prefix = 'preprints/Average-Sensitivity-of-Polynomial-Threshold-Functions-September-25-2026'
    pin = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    selected = json.loads((root / 'private/selected-tree.json').read_text())
    assert len(selected) == 16 and len({e['path'] for e in selected}) == 16
    assert all(e['path'] == prefix or e['path'].startswith(prefix + '/') for e in selected)
    blobs = {e['path']: e for e in selected if e['type'] == 'blob'}
    auth = json.loads((root / 'private/source-authentication.json').read_text())
    assert len(auth) == len(blobs) == 12
    assert {e['path'] for e in auth} == set(blobs)
    for e in auth:
        t = blobs[e['path']]
        assert e['sha'] == t['sha'] and e['size'] == t['size'] and e['mode'] == t['mode']
        assert e['copy'] == 'private/source/' + e['path'][len(prefix)+1:]
        assert e['url'] == 'https://raw.githubusercontent.com/openai/math/' + pin + '/' + e['path']
        b = (root / safe(e['copy'])).read_bytes()
        assert len(b) == t['size'] and sha(b) == e['sha256']
        assert hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == t['sha']

    allowed_context = ['frontier/campaigns/2026-10-14/discovery-arithmetic-r162aw-parent/assessment.md']
    allowed_context += ['frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162aw/private/' + s + '.md' for s in ['MATH', 'SOURCE-COMPARISON', 'READING-LIMITS', 'FINAL']]
    context = json.loads((root / 'private/context-bindings.json').read_text())
    assert len(context) == 5 and [e['original'] for e in context] == allowed_context
    project = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
    for i, e in enumerate(context):
        assert e['copy'] == 'private/context/' + str(i) + '-' + Path(e['original']).name
        original, copy = project / e['original'], root / safe(e['copy'])
        assert not original.is_symlink() and not copy.is_symlink()
        ob, cb = original.read_bytes(), copy.read_bytes()
        assert ob == cb and len(cb) == e['bytes'] and sha(cb) == e['sha256']
        assert original.stat().st_mode == e['original_mode'] and copy.stat().st_mode == e['copy_mode']

    records = json.loads((root / 'private/primary/access.json').read_text())
    records += json.loads((root / 'private/primary/second-access.json').read_text())
    last = json.loads((root / 'private/primary/third-access.json').read_text())
    records.append(dict(last, id='KKL2017'))
    seen = set()
    for e in records:
        if 'error' in e:
            continue
        name = e['id']
        assert re.fullmatch('[A-Za-z0-9]+', name) and name not in seen
        seen.add(name)
        b = (root / ('private/primary/' + name + '.pdf')).read_bytes()
        assert b.startswith(b'%PDF') and len(b) == e['bytes'] and sha(b) == e['sha256']
    assert len(seen) == 10

    c = root / 'private/controls'
    expected = json.loads((c / 'expected.json').read_text())
    ob, cb, tb = [(c / n).read_bytes() for n in ('original.txt', 'copy.txt', 'changed.txt')]
    assert sha(ob) == expected['original_sha256']
    assert (ob == cb) is expected['equal_copy']
    assert (sha(tb) == sha(ob)) is expected['changed_copy_matches']
    print(json.dumps({'artifact_authentication': 'PASS', 'payload_files': len(expected_files), 'whole_root_files': len(files), 'directories_including_root': len(dirs), 'payload_bytes': sum(e['bytes'] for e in expected_files.values()), 'canonical_blobs': len(auth), 'primary_pdfs': len(seen), 'exact_context_copies': len(context), 'mathematical_gate': 'NONE'}, sort_keys=True))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, required=True)
    p.add_argument('--final-sha256', required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--report-sha256', required=True)
    a = p.parse_args()
    run(a.root, a.final_sha256, a.manifest_sha256, a.report_sha256)
