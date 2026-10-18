#!/usr/bin/env python3
"""MIT. Reviewer's independent comparison of the r59 private source bodies with the
complete canonical preprints tree. Read-only. Identity only, not semantic coverage."""
import argparse, hashlib, json, os, sys
from pathlib import Path

TREE_SHA256 = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
DIRS = {
    'private/source117-1': 'preprints/Near-square-root-logarithmic-integrality-gaps-for-uniform-sparsest-cut-September-24-2026',
    'private/source117-2': 'preprints/Constant-factor-hardness-of-uniform-sparsest-cut-September-24-2026',
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tree', type=Path, required=True)
    ap.add_argument('--packet', type=Path, required=True)
    a = ap.parse_args()
    raw = a.tree.read_bytes()
    if hashlib.sha256(raw).hexdigest() != TREE_SHA256:
        raise SystemExit('FAIL: canonical tree digest mismatch')
    tree = json.loads(raw)
    if tree.get('truncated') is not False or len(tree['tree']) != 13223:
        raise SystemExit('FAIL: tree truncated or entry count mismatch')
    by = {e['path']: e for e in tree['tree']}
    rows, bad = [], []
    for local, prefix in DIRS.items():
        base = a.packet / local
        for dirpath, _, files in os.walk(base):
            for f in sorted(files):
                p = Path(dirpath) / f
                if p.is_symlink():
                    bad.append(str(p)); continue
                b = p.read_bytes()
                blob = hashlib.sha1(b'blob %d\0' % len(b) + b).hexdigest()
                path = prefix + '/' + p.relative_to(base).as_posix()
                e = by.get(path)
                ok = bool(e) and e['type'] == 'blob' and e['sha'] == blob and e.get('size') == len(b)
                rows.append({'path': path, 'git_blob_sha1': blob, 'bytes': len(b), 'match': ok})
                if not ok:
                    bad.append(path)
        canon = sorted(p[len(prefix) + 1:] for p, e in by.items()
                       if p.startswith(prefix + '/') and e['type'] == 'blob')
        held = sorted(Path(dirpath, f).relative_to(base).as_posix()
                      for dirpath, _, fs in os.walk(base) for f in fs)
        rows.append({'directory': prefix, 'canonical_blobs': len(canon),
                     'canonical_not_retrieved': sorted(set(canon) - set(held))})
    status = 'PASS' if not bad and sum(1 for r in rows if r.get('match')) == 20 else 'FAIL'
    print(json.dumps({'status': status, 'tree_sha256': TREE_SHA256, 'tree_entries': len(tree['tree']),
                      'truncated': tree['truncated'], 'matched_actual_bodies': sum(1 for r in rows if r.get('match')),
                      'mismatches': bad, 'rows': rows,
                      'scope': 'Git blob identity of actual local bodies only; not semantic reading or upstream truth.'},
                     indent=2))
    return status == 'PASS'


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
