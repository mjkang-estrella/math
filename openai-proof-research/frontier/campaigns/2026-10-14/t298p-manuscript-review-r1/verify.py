#!/usr/bin/env python3
"""Read-only, externally anchored integrity verifier for the T298P manuscript review r1. MIT.
Integrity only: it certifies no mathematics, reading, visual inspection, novelty or acceptance."""
import argparse, hashlib, json, os, re, stat
from pathlib import Path, PurePosixPath

AUTHOR_ANCHOR = '24a3e405e1bceda384a8b6a4e28f610809a4c9ec5b32b0a66e0277b24b2124fe'

def sha(b): return hashlib.sha256(b).hexdigest()

def need(ok, why):
    if not ok: raise SystemExit('FAIL: ' + why)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--anchor', required=True, help='externally supplied SHA256 of MANIFEST.json')
    ap.add_argument('--repo', type=Path, help='optional repository root: re-authenticate bound inputs')
    a = ap.parse_args()
    root = Path(os.path.abspath(__file__)).parent
    need(re.fullmatch('[0-9a-f]{64}', a.anchor) is not None, 'anchor syntax')
    mf = root / 'MANIFEST.json'
    st = mf.lstat()
    need(stat.S_ISREG(st.st_mode) and st.st_nlink == 1, 'manifest regular single-link file')
    raw = mf.read_bytes()
    need(sha(raw) == a.anchor, 'external manifest anchor')
    m = json.loads(raw)
    need(m.get('schema') == 'T298P-manuscript-review-r1', 'schema')
    need(m.get('verdict') == 'NEEDS_REVISION' and m.get('target_manifest_sha256') == AUTHOR_ANCHOR, 'bound verdict/target')
    expected = set(m['files']) | {'MANIFEST.json'}
    for name in expected:
        p = PurePosixPath(name)
        need(not p.is_absolute() and p.as_posix() == name and '..' not in p.parts and '.' not in p.parts, 'safe path ' + name)
    actual = set()
    for base, dirs, files in os.walk(root, followlinks=False):
        b = Path(base)
        for d in dirs:
            need(not (b / d).is_symlink(), 'symlink directory')
            need(d != '__pycache__', 'unexpected __pycache__')
        for f in files:
            q = b / f
            s = q.lstat()
            rel = q.relative_to(root).as_posix()
            need(stat.S_ISREG(s.st_mode) and s.st_nlink == 1, 'regular single-link payload ' + rel)
            actual.add(rel)
    need(actual == expected, 'exact sealed membership')
    for name, rec in m['files'].items():
        body = (root / name).read_bytes()
        need(len(body) == rec['bytes'], 'payload size ' + name)
        need(sha(body) == rec['sha256'], 'payload hash ' + name)
    v = json.loads((root / 'verdict.json').read_text())
    need(v['verdict'] == m['verdict'] and v['target_manifest_sha256'] == AUTHOR_ANCHOR, 'verdict.json consistency')
    repo_checked = False
    if a.repo:
        camp = a.repo.resolve() / 'frontier/campaigns/2026-10-14'
        auth = json.loads((root / 'checks/input-authentication.json').read_text())
        for row in auth['anchors']:
            need(sha((camp / row['path']).read_bytes()) == row['expected'], 'bound input ' + row['path'])
        for path, digest in auth['other_hashes'].items():
            need(sha((camp / path).read_bytes()) == digest, 'bound input ' + path)
        repo_checked = True
    print(json.dumps({'status': 'PASS', 'payload_files': len(m['files']), 'bound_inputs_checked': repo_checked,
                      'scope': 'file integrity only; no mathematical, reading, novelty or acceptance certification'}))

if __name__ == '__main__':
    main()
