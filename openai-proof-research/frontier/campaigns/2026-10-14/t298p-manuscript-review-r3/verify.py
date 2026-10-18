#!/usr/bin/env python3
"""Read-only review integrity check. Requires an external MANIFEST SHA256."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat


def sha(b):
    return hashlib.sha256(b).hexdigest()


def need(ok, reason):
    if not ok:
        raise SystemExit('FAIL: '+reason)


def regular(path):
    st = path.lstat()
    need(stat.S_ISREG(st.st_mode) and st.st_nlink == 1,
         'regular single-link payload '+str(path.name))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--anchor', required=True)
    p.add_argument('--repo', type=Path)
    a = p.parse_args()
    root = Path(__file__).absolute().parent
    need(re.fullmatch('[0-9a-f]{64}', a.anchor) is not None, 'anchor syntax')
    mf = root / 'MANIFEST.json'
    regular(mf)
    raw = mf.read_bytes()
    need(sha(raw) == a.anchor, 'external manifest anchor')
    manifest = json.loads(raw)
    need(manifest['excluded_top_level_directories'] == ['tmp'], 'exclusion policy')
    expected = set(manifest['files']) | {'MANIFEST.json'}
    for name in expected:
        q = Path(name)
        need(not q.is_absolute() and '..' not in q.parts and q.as_posix() == name,
             'safe payload path')
        need(q.parts[0] != 'tmp', 'transient exclusion')
    actual = set()
    for base, dirs, files in os.walk(root, followlinks=False):
        base = Path(base)
        if base == root:
            dirs[:] = [d for d in dirs if d != 'tmp']
        for name in dirs:
            need(not (base / name).is_symlink(), 'symlink directory')
        for name in files:
            file = base / name
            regular(file)
            actual.add(file.relative_to(root).as_posix())
    need(actual == expected, 'exact membership')
    for name, rec in manifest['files'].items():
        body = (root / name).read_bytes()
        need(len(body) == rec['bytes'], 'payload size '+name)
        need(sha(body) == rec['sha256'], 'payload hash '+name)
    checked = 0
    if a.repo:
        bound = json.loads((root / 'inputs.json').read_text())
        for name, rec in bound['files'].items():
            q = Path(name)
            need(not q.is_absolute() and '..' not in q.parts, 'safe external path')
            need(sha((a.repo / q).read_bytes()) == rec['sha256'], 'external input '+name)
            checked += 1
        need(json.loads((a.repo / 'sources/upstream.json').read_text())['commit'] == bound['upstream_pin'], 'upstream pin')
    need(json.loads((root / 'verdict.json').read_text())['verdict'] == 'NEEDS_REVISION', 'verdict consistency')
    print(json.dumps({'status': 'PASS', 'payload_files': len(manifest['files']),
                      'bound_inputs_checked': checked,
                      'scope': 'read-only byte integrity only; no theorem or acceptance certification'}))


if __name__ == '__main__':
    main()
