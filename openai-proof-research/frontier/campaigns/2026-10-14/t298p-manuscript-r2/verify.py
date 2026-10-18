#!/usr/bin/env python3
"""Read-only, externally anchored manuscript integrity check. MIT, Myeongjin Kang."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat


def sha(data):
    return hashlib.sha256(data).hexdigest()


def need(ok, reason):
    if not ok:
        raise SystemExit('FAIL: ' + reason)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--anchor', required=True, help='Externally obtained SHA256 of MANIFEST.json')
    p.add_argument('--repo', type=Path, help='Optional repository root: authenticate referenced inputs')
    a = p.parse_args()
    root = Path(__file__).absolute().parent
    need(re.fullmatch('[0-9a-f]{64}', a.anchor) is not None, 'anchor syntax')
    mf = root / 'MANIFEST.json'
    st = mf.lstat()
    need(stat.S_ISREG(st.st_mode) and st.st_nlink == 1, 'manifest regular single-link file')
    raw = mf.read_bytes()
    need(sha(raw) == a.anchor, 'external manifest anchor')
    manifest = json.loads(raw)
    need(manifest['excluded_top_level_directories'] == ['tmp'], 'exclusion policy')
    expected = set(manifest['files']) | {'MANIFEST.json'}
    for name in expected:
        q = Path(name)
        need(not q.is_absolute() and '..' not in q.parts and q.as_posix() == name,
             'safe manifest path')
        need(q.parts[0] != 'tmp', 'no transient payload')
    actual = set()
    for base, dirs, files in os.walk(root, followlinks=False):
        base = Path(base)
        if base == root:
            dirs[:] = [d for d in dirs if d != 'tmp']
        for d in dirs:
            need(not (base / d).is_symlink(), 'symlink directory')
        for name in files:
            file = base / name
            rel = file.relative_to(root).as_posix()
            st = file.lstat()
            need(stat.S_ISREG(st.st_mode) and st.st_nlink == 1, 'regular single-link payload ' + rel)
            actual.add(rel)
    need(actual == expected, 'exact sealed membership')
    for name, rec in manifest['files'].items():
        body = (root / name).read_bytes()
        need(len(body) == rec['bytes'], 'payload size ' + name)
        need(sha(body) == rec['sha256'], 'payload hash ' + name)
    inputs_checked = False
    if a.repo:
        repo = a.repo.resolve()
        inputs = json.loads((root / 'inputs.json').read_text())
        need(json.loads((repo / 'sources/upstream.json').read_text())['commit'] == inputs['upstream_pin'],
             'upstream pin')
        for name, rec in inputs['files'].items():
            need(sha((repo / name).read_bytes()) == rec['sha256'], 'external input ' + name)
        inputs_checked = True
    print(json.dumps({'status': 'PASS', 'payload_files': len(manifest['files']),
                      'external_inputs_checked': inputs_checked,
                      'scope': 'file integrity only; no mathematical, novelty, or acceptance verdict'}))

if __name__ == '__main__':
    main()
